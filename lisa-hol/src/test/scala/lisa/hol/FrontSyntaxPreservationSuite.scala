package lisa.hol

import lisa.SetTheoryLibrary
import lisa.hol.HOLHelperTheorems.𝔹
import lisa.hol.VarsAndFunctions.*
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.*
import lisa.utils.prooflib.ProofHelpers.*
import org.scalatest.funsuite.AnyFunSuite

class FrontSyntaxPreservationSuite extends AnyFunSuite:
  private given testLibrary: Library = SetTheoryLibrary

  private def sorry(statement: Sequent): Thm =
    BasicStep.Sorry(statement).destruct._1

  private def descendants(expression: Expr[?]): Iterator[Expr[?]] =
    Iterator.single(expression) ++ (expression match
      case App(function, argument) => descendants(function) ++ descendants(argument)
      case Abs(variable, body) => Iterator.single(variable) ++ descendants(body)
      case _ => Iterator.empty)

  private def statementDescendants(statement: Sequent): Iterator[Expr[?]] =
    (statement.left ++ statement.right).iterator.flatMap(descendants)

  test("HOL type constructors survive front theorem instantiation"):
    val typeVariable = TypeVariable(K.Identifier("preserved-type-variable"))
    val replacement = TypeVariable(K.Identifier("preserved-type-replacement"))
    val constructor = HOLPolymorphicType[Ind >>: Ind](
      K.Identifier("preserved-type-constructor"),
      Seq(typeVariable),
      sorry(() |- ⊤)
    )
    SetTheoryLibrary.addSymbol(constructor)
    val applied = constructor(typeVariable)
    val schema = sorry(() |- (applied === applied))

    val instance = schema.of(typeVariable := replacement)

    assert(statementDescendants(instance.statement).exists(_.eq(constructor)))
    assert(statementDescendants(instance.statement).exists(_.eq(replacement)))

  test("typed variables retain and substitute their type metadata in theorem statements"):
    val originalType = TypeVariable(K.Identifier("typed-variable-original-type"))
    val replacementType = TypeVariable(K.Identifier("typed-variable-replacement-type"))
    val typed = TypedVariable(K.Identifier("preserved-typed-variable"), originalType)
    val statement = TypeAssign(typed, originalType) |- (typed === typed)
    val schema = axiom(statement)

    val instance = schema.of(originalType := replacementType)
    val retained = statementDescendants(instance.statement).collectFirst { case variable: TypedVariable => variable }.get

    assert(retained.typ.eq(replacementType))
    assert(computeType(retained) eq replacementType)

  test("HOL type instantiation and cleanup work without metadata registries"):
    val originalType = TypeVariable(K.Identifier("inst-type-original"))
    val typed = TypedVariable(K.Identifier("inst-type-term"), originalType)
    val term = typed =:= typed
    val statement = HOLSequent(
      Set.empty,
      term,
      typeAssigns = Set(TypeAssign(typed, originalType)),
      typeVarsNonEmpty = Set(nonEmpty(originalType))
    )
    val premise = axiom(statement)

    val result = Proof.withContext:
      HOLSteps._INST_TYPE(Seq(originalType -> 𝔹), premise)

    assert(result.isValid, result.errors.map(_.message).mkString("\n"))
    val theorem = result.destruct._1
    val retainedVariables = statementDescendants(theorem.statement).collect { case variable: TypedVariable => variable }.toSeq
    assert(retainedVariables.nonEmpty)
    assert(retainedVariables.forall(variable => isSame(variable.typ, 𝔹)))
    assert(statementDescendants(theorem.statement).exists {
      case typ: HOLPolymorphicType[?] => typ.eq(𝔹)
      case _ => false
    })
