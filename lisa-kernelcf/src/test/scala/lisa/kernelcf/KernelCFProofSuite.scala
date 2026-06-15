package lisa.kernelcf

import lisa.kernelcf.fol.FOL.*
import lisa.kernelcf.proof.*
import lisa.kernelcf.proof.SequentCalculus.*
import org.scalatest.funsuite.AnyFunSuite

class KernelCFProofSuite extends AnyFunSuite:

  private def theoryWith(constants: Constant*): Theory =
    val theory = Theory.empty
    constants.foreach(theory.addSymbol)
    theory

  test("expression constructors are hashconsed"):
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
    assert(px eq px2)
    assert(l eq l2)
    assert(!(x eq y))
    assert(!(pAa eq pBB))
    assert(pAa != pBB)
    assert(px.uniqueNumber == px2.uniqueNumber)
    assert(isSame(Lambda(x, p(x))(y), p(y)))

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
