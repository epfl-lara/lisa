package lisa.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.*
import org.scalatest.funsuite.AnyFunSuite

class KernelProofSuite extends AnyFunSuite:

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

    assert(x eq x2)
    assert(p eq p2)
    if sys.props.get("lisa.hashcons.mode").contains("ids") then
      assert(!(px eq px2))
      assert(!(l eq l2))
    else
      assert(px eq px2)
      assert(l eq l2)
    assert(!(x eq y))
    assert(!(pAa eq pBB))
    assert(pAa != pBB)
    assert(px.uniqueNumber == px2.uniqueNumber)
    assert(l.uniqueNumber == l2.uniqueNumber)
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
      val cachesTrees = !sys.props.get("lisa.hashcons.mode").contains("ids")
      val usesTwoGenerations = !sys.props.get("lisa.hashcons.generations").contains("1")
      assert((f(x) eq before) == (cachesTrees && usesTwoGenerations))

      (limit until 2 * limit).foreach: index =>
        f(Variable(Identifier("eviction-filler", index), Ind))

      val after = f(x)
      val keepsIds = sys.props.get("lisa.hashcons.mode").exists(mode => mode == "ids" || mode == "hybrid")

      assert(!(before eq after))
      assert((before.uniqueNumber == after.uniqueNumber) == keepsIds)

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
