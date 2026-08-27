package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.ProofHelpers.*
import org.scalatest.funsuite.AnyFunSuite

class FrontSyntaxPreservationSuite extends AnyFunSuite:

  given testLibrary: Library = new Library

  private final class TaggedConstant[S: Sort](id: Identifier) extends Constant[S](id)

  private final class TaggedVariable(id: Identifier) extends Variable[Ind](id):
    override def rename(newId: Identifier): TaggedVariable = TaggedVariable(newId)

  private def containsReference(expression: Expr[?], target: Expr[?]): Boolean =
    expression.eq(target) || (expression match
      case App(function, argument) => containsReference(function, target) || containsReference(argument, target)
      case Abs(variable, body) => variable.eq(target) || containsReference(body, target)
      case _ => false)

  private def assertContains(statement: Sequent, target: Expr[?]): Unit =
    assert(
      (statement.left ++ statement.right).exists(containsReference(_, target)),
      s"Expected $statement to retain ${target.getClass.getName}."
    )

  private def assertValid(judgement: ProofJudgement): Thm =
    assert(judgement.isValid, judgement.errors.map(_.message).mkString("\n"))
    judgement.destruct._1

  test("a basic step retains front subclasses"):
    val tagged = TaggedConstant[Ind](K.Identifier("basic-tag"))
    val formula = tagged === tagged

    val theorem = assertValid(BasicStep.Hypothesis(formula |- formula))

    assertContains(theorem.statement, tagged)

  test("an inferred basic step retains its requested front statement"):
    val tagged = TaggedConstant[Ind](K.Identifier("inferred-basic-tag"))
    val pivot = tagged === tagged
    val result = tagged === variable[Ind]
    val first = BasicStep.Sorry(() |- pivot).destruct._1
    val second = BasicStep.Sorry(pivot |- result).destruct._1

    val theorem = assertValid(BasicStep.Cut(first, second)(() |- result))

    assert(theorem.statement == (() |- result))
    assertContains(theorem.statement, tagged)

  test("a single have retains front subclasses"):
    val tagged = TaggedConstant[Ind](K.Identifier("have-tag"))
    val formula = tagged === tagged

    val result = Subproof {
      have(formula |- formula) by BasicStep.Hypothesis
    }

    assertContains(assertValid(result).statement, tagged)

  test("a nested proof context inherits front assumptions without a kernel round-trip"):
    val tagged = TaggedConstant[Ind](K.Identifier("context-tag"))
    val assumption = tagged === tagged

    val result = Proof.withContext: outer ?=>
      outer.assume(assumption)
      outer.withSubcontext(): inner ?=>
        assert(inner.assumptions.exists(containsReference(_, tagged)))
        ProofJudgement(have(() |- assumption) by BasicStep.Hypothesis)

    assertContains(assertValid(result).statement, tagged)

  test("a have subproof returns the requested front statement"):
    val tagged = TaggedConstant[Ind](K.Identifier("subproof-tag"))
    val assumption = tagged === tagged

    val result = Proof.withContext: proof ?=>
      proof.assume(assumption)
      val theorem = have(() |- assumption) subproof {
        have(() |- assumption) by BasicStep.Hypothesis
      }
      ProofJudgement(theorem)

    result match
      case carrier: SoftCarrier[?] => assertContains(carrier.statement, tagged)
      case _: FatalCarrier => fail("The have subproof unexpectedly produced a fatal carrier.")
    assertContains(assertValid(result).statement, tagged)

  test("a theorem retains its declared front statement"):
    given OutputManager = StringOutputManager()
    val tagged = TaggedConstant[Ind](K.Identifier("theorem-tag"))
    val formula = tagged === tagged

    val retainedTheorem = Theorem(() |- formula) {
      have(() |- formula) by BasicStep.Sorry
    }

    assertContains(retainedTheorem.statement, tagged)
    assertContains(retainedTheorem.thm.statement, tagged)

  test("Thm instantiation substitutes the retained front statement"):
    val predicate = TaggedConstant[Ind >>: Prop](K.Identifier("instance-predicate"))
    val variable = TaggedVariable(K.Identifier("instance-variable"))
    val argument = TaggedConstant[Ind](K.Identifier("instance-argument"))
    val schema = BasicStep.Sorry(() |- predicate(variable)).destruct._1

    val instance = schema.of(variable := argument)

    assert(instance.statement == (() |- predicate(argument)))
    assertContains(instance.statement, predicate)
    assertContains(instance.statement, argument)

  test("Theorem instantiation retains front subclasses"):
    given OutputManager = StringOutputManager()
    val predicate = TaggedConstant[Ind >>: Prop](K.Identifier("theorem-instance-predicate"))
    val variable = TaggedVariable(K.Identifier("theorem-instance-variable"))
    val argument = TaggedConstant[Ind](K.Identifier("theorem-instance-argument"))
    val instantiableTheorem = Theorem(() |- predicate(variable)) {
      have(() |- predicate(variable)) by BasicStep.Sorry
    }

    val instance = instantiableTheorem.of(variable := argument)

    assert(instance.statement == (() |- predicate(argument)))
    assertContains(instance.statement, predicate)
    assertContains(instance.statement, argument)

  test("a definition theorem retains the original front expression"):
    val body = TaggedConstant[Ind](K.Identifier("definition-body"))
    testLibrary.addSymbol(body)

    val (_, definition) = testLibrary.define("front-preserving-definition", body)

    assertContains(definition.statement, body)

  test("a functional definition retains front subclasses in its body and binder"):
    val body = TaggedConstant[Ind](K.Identifier("functional-definition-body"))
    val bound = TaggedVariable(K.Identifier("functional-definition-bound"))
    testLibrary.addSymbol(body)

    val (_, definition) = testLibrary.define("front-preserving-functional-definition", λ(bound, body))

    assertContains(definition.statement, body)
    assertContains(definition.statement, bound)

  test("a front theorem rejects an unrelated kernel statement"):
    val formula = variable[Prop]
    val kernel = K.sorry(using testLibrary.theory)(K.Sequent(Set.empty, Set(K.top)))

    assertThrows[IllegalArgumentException](Thm(() |- formula, kernel))
