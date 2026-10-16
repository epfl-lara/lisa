package lisa.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.*
import org.scalatest.funsuite.AnyFunSuite

class KernelProofSuite extends AnyFunSuite:

  private val hashconsMode = sys.props.getOrElse("lisa.hashcons.mode", "hybrid")
  private val hashconsEnabled =
    !sys.props.get("lisa.hashcons").exists(value => value == "false" || value == "0") &&
      !sys.env.get("LISA_HASHCONS").exists(value => value == "false" || value == "0")

  private def theoryWith(constants: Constant*): Theory =
    val theory = Theory.empty
    constants.foreach(theory.addSymbol)
    theory

  test("expression constructors preserve configured identity semantics"):
    val x = Variable(Identifier("x"), Ind)
    val x2 = Variable(Identifier("x"), Ind)
    val y = Variable(Identifier("y"), Ind)
    val p = Constant(Identifier("P"), Ind -> Prop)
    val p2 = Constant(Identifier("P"), Ind -> Prop)
    val pAa = Constant(Identifier("Aa"), Ind)
    val pBB = Constant(Identifier("BB"), Ind)
    val px = p(x)
    val px2 = p2(x2)
    val l = Lambda(x, px)
    val l2 = Lambda(x2, px2)

    assert((x eq x2) == hashconsEnabled)
    assert((p eq p2) == hashconsEnabled)
    if !hashconsEnabled || hashconsMode == "ids" then
      assert(!(px eq px2))
      assert(!(l eq l2))
    else
      assert(px eq px2)
      assert(l eq l2)
    assert(!(x eq y))
    assert(!(pAa eq pBB))
    assert(pAa != pBB)
    assert((px.uniqueNumber == px2.uniqueNumber) == hashconsEnabled)
    assert((l.uniqueNumber == l2.uniqueNumber) == hashconsEnabled)
    assert(isSame(Lambda(x, p(x))(y), p(y)))

  test("composite identities survive tree-cache eviction only with canonical IDs"):
    val limit = sys.props.get("lisa.hashcons.max").flatMap(_.toIntOption).getOrElse(0)
    if limit > 0 && limit <= 64 then
      val f = Constant(Identifier("eviction-f"), Ind -> Ind)
      val x = Variable(Identifier("eviction-x"), Ind)
      val before = f(x)

      (0 until limit).foreach: index =>
        f(Variable(Identifier("eviction-filler", index), Ind))

      // First rollover retains the completed generation.
      val cachesTrees = hashconsEnabled && hashconsMode != "ids"
      val usesTwoGenerations = !sys.props.get("lisa.hashcons.generations").contains("1")
      assert((f(x) eq before) == (cachesTrees && usesTwoGenerations))

      (limit until 2 * limit).foreach: index =>
        f(Variable(Identifier("eviction-filler", index), Ind))

      val after = f(x)
      val keepsIds = hashconsEnabled && (hashconsMode == "ids" || hashconsMode == "hybrid")

      assert(!(before eq after))
      assert((before.uniqueNumber == after.uniqueNumber) == keepsIds)
      assert(before == after)
      assert(before.hashCode == after.hashCode)
      assert(Set(before).contains(after))

  test("substitution freshens binders past variables already in their bodies"):
    val bound = Variable(Identifier("x", 4), Ind)
    val bodyFree = Variable(Identifier("x", 5), Ind)
    val source = Variable(Identifier("source"), Ind)
    val predicate = Constant(Identifier("capture-predicate"), Ind -> (Ind -> Prop))
    val abstraction = Lambda(bound, predicate(bodyFree)(source))

    val result = substituteVariables(abstraction, Map(source -> bound))

    result match
      case Lambda(renamed, body) =>
        assert(renamed.id == Identifier("x", 6))
        assert(body.freeVariables.contains(bodyFree))
      case _ => fail(s"Expected a lambda, got $result")

  test("hypothesis builds a theorem in the current theory"):
    val p = Constant(Identifier("p"), Prop)
    given theory: Theory = theoryWith(p)
    val statement = Sequent(Set(p), Set(p))

    val thm = Hypothesis.apply(using theory)(statement, p).toOption.get

    assert(thm.statement == statement)
    assert(thm.theory eq theory)
    assert(thm.axioms.isEmpty)
    assert(!thm.usesSorry)

  test("theorems from different theories cannot compose"):
    val p = Constant(Identifier("p"), Prop)
    val q = Constant(Identifier("q"), Prop)
    val leftTheory = theoryWith(p, q)
    val rightTheory = theoryWith(p, q)

    val left = Hypothesis.apply(using leftTheory)(Sequent(Set(p), Set(p)), p).toOption.get
    val right = Hypothesis.apply(using rightTheory)(Sequent(Set(q), Set(q)), q).toOption.get

    val result = Cut.apply(using leftTheory)(Sequent(Set(p, q), Set(q)), left, right, p)

    assert(result.left.exists(_.isInstanceOf[TheoryMismatch]))

  test("definition registers a fresh symbol"):
    val a = Constant(Identifier("a"), Ind)
    val c = Constant(Identifier("c"), Ind)
    val theory = theoryWith(a)

    val thm = Definition.apply(using theory)(c, Seq.empty, a).toOption.get

    assert(theory.defines(c))
    assert(theory.getDefinition(c).contains(thm))
    assert(thm.statement == Sequent(Set.empty, Set(equality(c)(a))))

  test("definition rejects expressions outside the theory"):
    val a = Constant(Identifier("a"), Ind)
    val c = Constant(Identifier("c"), Ind)
    val theory = Theory.empty

    val result = Definition.apply(using theory)(c, Seq.empty, a)

    assert(result.left.exists(_.isInstanceOf[Definition.ExpressionNotInTheory]))

  test("definition rejects self-reference and forward references without registering a symbol"):
    given theory: Theory = Theory.empty
    val c = Constant(Identifier("recursive-definition"), Prop)
    val d = Constant(Identifier("forward-definition"), Prop)

    assert(Definition(c, Seq.empty, neg(c)).isLeft)
    assert(Definition(c, Seq.empty, d).isLeft)
    assert(theory.getSymbol(c.id).isEmpty)
    assert(theory.getDefinition(c).isEmpty)

  test("declaring a symbol precludes defining it, including recursive definitions"):
    given theory: Theory = Theory.empty
    val c = Constant(Identifier("declared-definition"), Prop)
    theory.addSymbol(c)

    assert(Definition(c, Seq.empty, neg(c)) == Left(Definition.AlreadyDefined(c)))
    assert(Definition(c, Seq.empty, top) == Left(Definition.AlreadyDefined(c)))
    assert(theory.getDefinition(c).isEmpty)

  test("definition rejects occupied names even at a different sort"):
    given theory: Theory = Theory.empty
    val original = Constant(Identifier("occupied-definition"), Ind)
    val replacement = Constant(original.id, Prop)
    theory.addSymbol(original)

    assert(Definition(replacement, Seq.empty, top) == Left(Definition.AlreadyDefined(replacement)))
    assert(theory.getSymbol(original.id).contains(original))

  test("definitions can depend on earlier definitions and declared primitives"):
    given theory: Theory = Theory.empty
    val primitive = Constant(Identifier("definition-primitive"), Prop)
    val first = Constant(Identifier("definition-first"), Prop)
    val second = Constant(Identifier("definition-second"), Prop)
    theory.addSymbol(primitive)

    assert(Definition(first, Seq.empty, neg(primitive)).isRight)
    assert(Definition(second, Seq.empty, neg(first)).isRight)
    assert(Definition(first, Seq.empty, second) == Left(Definition.AlreadyDefined(first)))

  test("higher-sort alpha-renaming preserves same-named free individuals"):
    val bound = Variable(Identifier("sorted-binder"), Ind -> Ind)
    val renamed = Variable(Identifier("renamed-binder"), Ind -> Ind)
    val free = Variable(bound.id, Ind)
    val otherFree = Variable(renamed.id, Ind)

    assert(isSame(Lambda(bound, bound(free)), Lambda(renamed, renamed(free))))
    assert(isSame(Lambda(bound, free), Lambda(renamed, free)))
    assert(!isSame(Lambda(bound, free), Lambda(renamed, otherFree)))

    given theory: Theory = Theory.empty
    val p = Variable(Identifier("observe-abstraction"), ((Ind -> Ind) -> Ind) -> Prop)
    val left = p(Lambda(bound, free))
    val right = p(Lambda(renamed, otherFree))
    val premise = Hypothesis(Sequent(Set(left), Set(left)), left).toOption.get
    assert(Restate(Sequent(Set(left), Set(right)), premise).isLeft)

  test("reconstructed variables remain visible to quantifier freshness checks"):
    given theory: Theory = Theory.empty
    val x = Variable(Identifier("freshness-x"), Ind)
    val p = Variable(Identifier("freshness-p"), Ind -> Prop)
    val variables = x +: (1 to 6).map(i => Variable(Identifier("freshness-filler", i), Ind))
    val formula = variables.map(p(_)).reduce(and(_)(_))
    val reconstructed = Variable(Identifier("freshness-x"), Ind)
    val premise = Hypothesis(Sequent(Set(formula), Set(formula)), formula).toOption.get

    assert(x == reconstructed)
    assert(x.hashCode == reconstructed.hashCode)
    assert(formula.freeVariables.contains(reconstructed))
    assert(RightForall(Sequent(Set(formula), Set(forall(Lambda(reconstructed, formula)))), premise, formula, reconstructed).isLeft)
