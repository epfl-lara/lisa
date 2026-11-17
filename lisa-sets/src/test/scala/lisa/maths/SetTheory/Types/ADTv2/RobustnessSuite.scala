package lisa.maths.SetTheory.Types.ADTv2

import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2._
import lisa.maths.SetTheory.Types.ADTv2.library.bool
import lisa.maths.SetTheory.Types.ADTv2.library.cons
import lisa.maths.SetTheory.Types.ADTv2.library.list
import lisa.maths.SetTheory.Types.ADTv2.library.nat
import lisa.maths.SetTheory.Types.ADTv2.library.nil
import lisa.maths.SetTheory.Types.ADTv2.library.succ
import lisa.maths.SetTheory.Types.ADTv2.library.tru
import lisa.maths.SetTheory.Types.ADTv2.library.zero
import lisa.maths.SetTheory.Types.Tactics
import lisa.maths.SetTheory.Types.TypingHelpers
import lisa.utils.prooflib.OutputManager
import org.scalatest.funsuite.AnyFunSuite

/**
 * Exercises binder collisions and recursive equality beneath nested abstractions.
 */
class RobustnessSuite extends AnyFunSuite:
  private given OutputManager = new OutputManager:
    val stringWriter = new java.io.StringWriter
    def finishOutput(exception: Exception): Nothing = throw exception

  private val ignored, point, inner, u, v = variable[Ind]

  for name <- Seq(
      "f0",
      "nVar",
      "kVar",
      "jVar",
      "hist",
      "yVar",
      "a",
      "f",
      "x",
      "y",
      "h",
      "defVar",
      "pointParam",
      "indexParam",
      "sliceVar",
      "pointInput",
      "leftFun",
      "rightFun",
      "vVar",
      "pairWitness",
      "k1",
      "k2"
    )
  do
    test(s"function parameter $name remains free throughout proof construction"):
      val parameter = Variable[Ind](name)
      val defined = fun(parameter)(nat.specialize(), list(parameter))(using sourcecode.Name(s"robustParameter/$name")) {
        Case(zero):
          nil(parameter)
        Case(succ, ignored):
          nil(parameter)
      }
      val computation = Theorem(defined(bool) * (succ * zero) === nil(bool)) {
        have(thesis) by Tautology.from(defined.elim(succ).of(bool).of(ignored := zero), zero.intro)
      }
      assert(!defined.intro.withSorry && !computation.withSorry)

  test("recursive functions preserve a type parameter named like the seed binder"):
    val parameter = Variable[Ind]("f0")
    val robustRecursiveParameter = recFun(parameter)(nat.specialize(), list(parameter)) { self =>
      Case(zero):
        nil(parameter)
      Case(succ, ignored):
        self * ignored
    }
    val computation = Theorem(robustRecursiveParameter(bool) * (succ * zero) === robustRecursiveParameter(bool) * zero) {
      have(thesis) by Tautology.from(robustRecursiveParameter.elim(succ).of(bool).of(ignored := zero), zero.intro)
    }
    assert(!robustRecursiveParameter.intro.withSorry && !computation.withSorry)

  for name <- Seq("x", "h", "nVar", "head1", "head2", "tail1", "tail2") do
    test(s"specialized domain parameter $name is distinct from height and constructor variables"):
      val parameter = Variable[Ind](name)
      val defined = fun(parameter)(list.specialize(parameter), list(parameter))(using sourcecode.Name(s"robustDomain/$name")) {
        Case(nil):
          nil(parameter)
        Case(cons, u, v):
          nil(parameter)
      }
      val computation = Theorem(defined(bool) * nil(bool) === nil(bool)) {
        have(thesis) by Tautology.from(defined.elim(nil).of(bool))
      }
      assert(!defined.intro.withSorry && !computation.withSorry)

  test("specialization preserves a value binder named like the original type parameter"):
    val parameter = Variable[Ind]("robustElement")
    val sourceParameter = list.typeVariablesSeq.head
    val robustSourceParameter = fun(parameter)(list.specialize(parameter), list(parameter)) {
      Case(nil):
        nil(parameter)
      Case(cons, sourceParameter, inner):
        cons(parameter) * sourceParameter * inner
    }
    val input = cons(bool) * tru * nil(bool)
    val computation = Theorem(robustSourceParameter(bool) * input === input) {
      have(thesis) by Tautology.from(
        robustSourceParameter.elim(cons).of(bool).of(sourceParameter := tru, inner := nil(bool)),
        tru.intro,
        nil.intro.of(bool)
      )
    }
    assert(!robustSourceParameter.intro.withSorry && !computation.withSorry)

  test("nested recursion preserves a type parameter named like a constructor argument"):
    val parameter = Variable[Ind]("head2")
    val robustNestedParameter = recFun(parameter)(list.specialize(parameter), list(parameter)) { self =>
      Case(nil):
        nil(parameter)
      Case(cons, u, nil(parameter)):
        nil(parameter)
      Case(cons, u, cons(parameter) * v * inner):
        self * inner
    }
    val tail = cons(bool) * tru * nil(bool)
    val input = cons(bool) * tru * tail
    val branch = robustNestedParameter.patternFor(Case(cons, u, cons(parameter) * v * inner))
    val computation = Theorem(robustNestedParameter(bool) * input === robustNestedParameter(bool) * nil(bool)) {
      val tailTyped = have(tail :: list(bool)) by Tactics.Typecheck.prove
      have(thesis) by Tautology.from(
        robustNestedParameter.elim(branch).of(bool).of(u := tru, branch.topBinders(1) := tail, v := tru, inner := nil(bool)),
        tru.intro,
        nil.intro.of(bool),
        tailTyped
      )
    }
    assert(!robustNestedParameter.intro.withSorry && !computation.withSorry)

  test("constructor predicates do not capture another constructor's arguments"):
    val declaration = adt(
      "robustCarrierCapture",
      "A",
      Seq(
        ("one", Seq(("x2", "A"))),
        ("two", Seq(("x", "A"), ("y", "A")))
      )
    )
    val Seq(one, two) = declaration.constructors: @unchecked
    assert(!one.intro.withSorry && !two.intro.withSorry)
    assert(!one.injectivity.withSorry && !two.injectivity.withSorry)
    assert(!declaration.elim.withSorry && !declaration.disjointness(one, two).withSorry)

  for depth <- Seq(2, 3) do
    test(s"recursive body equality works beneath $depth nested lambdas"):
      val binders = (0 until depth).map(i => Variable[Ind](s"robustLambdaArg$i"))
      def abstractions(body: Expr[Ind]): Expr[Ind] =
        binders.foldRight(body)((binder, innerBody) => TypingHelpers.fun(binder :: nat.term, innerBody))
      def applications(head: Expr[Ind]): Expr[Ind] = binders.foldLeft(head)(_ * _)
      val resultType = binders.foldRight(nat.term: Expr[Ind])((_, typ) => nat.term ->: typ)
      val defined = recFun(nat, resultType)(using sourcecode.Name(s"robustNestedLambdas$depth")) { self =>
        Case(zero):
          abstractions(zero)
        Case(succ, ignored):
          abstractions(succ * applications(self * ignored))
      }
      val computation = Theorem(defined * (succ * zero) === abstractions(succ * applications(defined * zero))) {
        have(thesis) by Tautology.from(defined.elim(succ).of(ignored := zero), zero.intro)
      }
      assert(!defined.intro.withSorry && !computation.withSorry)

  for ambient <- Seq(succ.semantic.variables2.head, Variable[Ind]("t")) do
    test(s"induction preserves the ambient variable ${ambient.id}"):
      val premise = ambient === zero
      val checked = Theorem((point :: nat, premise) |- premise) {
        have(thesis) by Induction(point, nat) {
          Case(zero) subproof { have(thesis) by Hypothesis }
          Case(succ, zero) subproof { have(thesis) by Hypothesis }
          Case(succ, succ * inner) subproof { have(thesis) by Hypothesis }
        }
      }
      assert(!checked.withSorry)
