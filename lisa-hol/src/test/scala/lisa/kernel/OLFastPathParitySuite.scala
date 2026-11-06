package lisa.kernel

import lisa.kernel.fol.FOL.*
import org.scalatest.funsuite.AnyFunSuite

class OLFastPathParitySuite extends AnyFunSuite:
  private val p = Variable(Identifier("fast-p"), Prop)
  private val q = Variable(Identifier("fast-q"), Prop)
  private val r = Variable(Identifier("fast-r"), Prop)

  // Retain the constructing antichain algorithm as an oracle for the split-sequence path.
  private def originalReduceList(children: Seq[SimpleExpression], polarity: Boolean): List[SimpleExpression] =
    val context = SimpleAnd(children, polarity)
    def expand(child: SimpleExpression): Seq[SimpleExpression] = child match
      case SimpleAnd(cs, true) => cs.flatMap(expand)
      case SimpleAnd(cs, false) if polarity =>
        cs.map(getInversePolar).find(latticesLEQ(context, _)).fold(Seq(child))(expand)
      case SimpleAnd(cs, false) =>
        cs.find(latticesLEQ(_, context)).fold(Seq(child))(c => expand(getInversePolar(c)))
      case _ => Seq(child)
    var remaining = children.foldLeft(Seq.empty[SimpleExpression])((rest, child) => expand(child) ++ rest)
    var accepted = List.empty[SimpleExpression]
    while remaining.nonEmpty do
      val current = remaining.head
      remaining = remaining.tail
      if !latticesLEQ(SimpleAnd(remaining ++ accepted, true), current) then accepted = current :: accepted
    accepted

  test("split-sequence antichain reduction agrees with constructing conjunctions"):
    val atoms = Vector(p, q, r).map(simpleReducedForm)
    val literals = atoms ++ atoms.map(getInversePolar) ++ Vector(SimpleLiteral(true), SimpleLiteral(false))
    val nested = for a <- atoms; b <- atoms; polarity <- Vector(true, false) yield SimpleAnd(Seq(a, b), polarity)
    val contexts = Vector(Seq.empty[SimpleExpression]) ++
      literals.map(Seq(_)) ++
      (for a <- literals; b <- literals; c <- literals yield Seq(a, b, c)) ++
      (for a <- nested; b <- literals yield Seq(a, b, getInversePolar(a)))
    for children <- contexts; polarity <- Vector(true, false) do
      assert(reduceList(children, polarity) == originalReduceList(children, polarity), s"$children, $polarity")

  test("identity shortcuts retain negative comparisons and beta equivalence"):
    val x = Variable(Identifier("fast-x"), Ind)
    assert(isSame(p, p))
    assert(isImplying(p, p))
    assert(!isSame(p, q))
    assert(!isImplying(p, q))
    assert(isSame(Lambda(x, p)(x), p))

  test("recursive comparisons retain quantifier monotonicity and embedded formulas"):
    val x = Variable(Identifier("fast-x"), Ind)
    val y = Variable(Identifier("fast-y"), Ind)
    val pred = Constant(Identifier("fast-P"), Ind -> Prop)
    val both = forall(Lambda(x, and(pred(x))(p)))
    val one = forall(Lambda(y, pred(y)))
    assert(isImplying(both, one))
    assert(isImplying(neg(one), neg(both)))
    val f = Constant(Identifier("fast-f"), Prop -> Ind)
    assert(isSame(f(and(p)(q)), f(and(q)(p))))
    assert(!isSame(f(p), f(q)))

  test("public implication and order checks still reject non-propositions before identity"):
    val x = Variable(Identifier("fast-x"), Ind)
    val term = simpleReducedForm(x)
    val proposition = simpleReducedForm(p)
    intercept[IllegalArgumentException](isImplying(x, x))
    intercept[IllegalArgumentException](isImplying(p, x))
    intercept[IllegalArgumentException](latticesLEQ(term, term))
    intercept[IllegalArgumentException](latticesLEQ(proposition, term))
    intercept[IllegalArgumentException](latticesLEQ(term, proposition))
