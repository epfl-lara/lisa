package lisa.hol

import lisa.SetTheoryLibrary
import lisa.hol.HOLHelperTheorems.𝔹
import lisa.hol.VarsAndFunctions.*
import lisa.hol.basics.Connectives.hand
import lisa.hol.basics.Inductive.hOneOne
import lisa.maths.SetTheory.Functions.Pi.->:
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

  private def typedConstant(name: String): TypedConstant =
    val raw = Constant[Ind](K.Identifier(name))
    SetTheoryLibrary.addSymbol(raw)
    TypedConstant(raw.id, 𝔹, sorry(() |- TypeAssign(raw, 𝔹)))

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
    val schema = sorry(statement)

    val instance = schema.of(originalType := replacementType)
    val retained = statementDescendants(instance.statement).collectFirst { case variable: TypedVariable => variable }.get

    assert(retained.typ.eq(replacementType))
    assert(computeType(retained) eq replacementType)

  test("HOL transitivity preserves typed constants"):
    val left = typedConstant("transitivity-left")
    val middle = typedConstant("transitivity-middle")
    val right = typedConstant("transitivity-right")
    val first = sorry(HOLSequent(Set.empty, left =:= middle))
    val second = sorry(HOLSequent(Set.empty, middle =:= right))

    HOLSteps.HOLProofType.resetCache()
    val result = Proof.withContext:
      ExtendedHOLSteps._TRANS(first, second)

    assert(result.isValid, result.errors.map(_.message).mkString("\n"))
    val retained = statementDescendants(result.destruct._1.statement).collect { case constant: TypedConstant => constant }.toSeq
    val retainedLeft = retained.find(_.eq(left)).get
    val retainedRight = retained.find(_.eq(right)).get
    assert(computeType(retainedLeft) eq 𝔹)
    assert(computeType(retainedRight) eq 𝔹)

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
    val premise = sorry(statement)

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

  test("HOL typing preserves a free same-named variable while freshening a binder"):
    val typeA = TypeVariable(K.Identifier("typing-shadow-A"))
    val typeB = TypeVariable(K.Identifier("typing-shadow-B"))
    val bound = TypedVariable(K.Identifier("x-prime", 1), typeA)
    val function = TypedVariable(K.Identifier("x-prime", 2), typeA ->: typeB)
    val argument = TypedVariable(K.Identifier("x", 1), typeA)
    val otherFunction = TypedVariable(K.Identifier("f", 2), typeA ->: typeB)
    val predicate = TypedVariable(K.Identifier("P", 3), typeA ->: typeB ->: 𝔹)
    val source = TypedVariable(K.Identifier("source"), typeA)
    val body = hand * (predicate * source * (otherFunction * argument)) * (predicate * bound * (function * argument))
    val term = VarsAndFunctions.fun(bound, body).substitute(source := bound)

    assert(term.freeVars.contains(function))

    val result = Proof.withContext:
      Subproof:
        have(HOLSteps.HOLProofType(term))

    assert(result.isValid, result.errors.map(_.message).mkString("\n"))

  test("HOL typing cache distinguishes equal kernel terms with different HOL types"):
    val typeA = TypeVariable(K.Identifier("typing-cache-A"))
    val typeB = TypeVariable(K.Identifier("typing-cache-B"))
    val identifier = K.Identifier("typing-cache-term")
    val termA = TypedVariable(identifier, typeA)
    val termB = TypedVariable(identifier, typeB)

    val result = Proof.withContext:
      HOLSteps.HOLProofType.resetCache()
      val typingA = HOLSteps.HOLProofType(termA)
      val typingB = HOLSteps.HOLProofType(termB)
      Subproof:
        have(typingA)
        have(typingB)

    assert(result.isValid, result.errors.map(_.message).mkString("\n"))
    val typings = result.destruct._1.statement
    assert(typings.right.exists(isSame(_, termB :: typeB)))

  test("polymorphic typing splits conjunctive requirements"):
    val typeA = TypeVariable(K.Identifier("typing-conjunction-A"))
    val typeB = TypeVariable(K.Identifier("typing-conjunction-B"))

    val result = Proof.withContext:
      Subproof:
        have(HOLSteps.HOLProofType(hOneOne(typeA)(typeB)))

    assert(result.isValid, result.errors.map(_.message).mkString("\n"))
    val assumptions = result.destruct._1.statement.left
    assert(assumptions.exists(isSame(_, nonEmpty(typeA))))
    assert(assumptions.exists(isSame(_, nonEmpty(typeB))))
    assert(!assumptions.exists(isSame(_, nonEmpty(typeA) /\ nonEmpty(typeB))))
