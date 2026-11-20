package lisa.maths.SetTheory.Types.ADT.encoding

import lisa.maths.SetTheory.Functions.Predef.app
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.ProofChecks._
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.ADT.syntax.AST.ConstructorArg
import lisa.maths.SetTheory.Types.ADT.syntax.AST.SelfRef
import lisa.maths.SetTheory.Types.ADT.syntax.AST.TypeArg
import lisa.utils.prooflib.OutputManager
import lisa.utils.prooflib.StringOutputManager
import org.scalatest.funsuite.AnyFunSuite

/**
 * Executes the common-height proof for each combination of recursive and payload fields.
 */
class CommonHeightSuite extends AnyFunSuite:
  private given OutputManager = new StringOutputManager

  private def checkCommonHeight(name: String, fields: Seq[ConstructorArg]): Unit =
    val A, B = variable[Ind]
    val variables = fields.indices.map(i => Variable[Ind](s"field$i"))
    val alternatives = fields.indices.map(i => Variable[Ind](s"otherField$i"))
    val constructor = new SyntacticConstructor(fields, variables, alternatives, 0, name)
    val declaration = new SyntacticADT(name, Seq(constructor), Seq(A, B))
    val expected = declaration.isHeight(h) |- (
      declaration.constructorVarsInDomain(constructor, declaration.term) <=>
        ∃(n, n ∈ N /\ declaration.constructorVarsInDomain(constructor, app(h)(n)))
    )
    val theorem = Theorem.generated(expected) {
      val before = lisa.SetTheoryLibrary.theorems.all.size
      val commonHeight = declaration.termsHaveHeight(constructor, h)
      assert(lisa.SetTheoryLibrary.theorems.all.size == before)
      have(thesis) by Restate.from(commonHeight)
    }
    assert(!theorem.hasErrorsOrSorry)
    assert(!declaration.intro(constructor).hasErrorsOrSorry)

  test("nullary constructors have a common height"):
    checkCommonHeight("commonHeightNullary", Seq.empty)

  test("payload-only constructors have a common height without recursive fields"):
    checkCommonHeight("commonHeightPayloads", Seq(TypeArg("A"), TypeArg("B"), TypeArg("A"), TypeArg("B")))

  test("interleaved payload and recursive fields share a common height"):
    checkCommonHeight("commonHeightMixed", Seq(TypeArg("A"), SelfRef, TypeArg("B"), SelfRef, TypeArg("A")))

  test("several recursive fields share a common height"):
    checkCommonHeight("commonHeightRecursive", Seq(SelfRef, SelfRef, SelfRef))

  test("argument renaming preserves simultaneous type, argument, and height substitutions"):
    val A, payload, recursive, otherPayload, otherRecursive = variable[Ind]
    val name = "commonHeightSimultaneous"
    val constructor = new SyntacticConstructor(
      Seq(TypeArg("A"), SelfRef),
      Seq(payload, recursive),
      Seq(otherPayload, otherRecursive),
      0,
      name
    )
    val declaration = new SyntacticADT(name, Seq(constructor), Seq(A))
    val schema = declaration.isHeight(h) |- (
      declaration.constructorVarsInDomain(constructor, declaration.term) <=>
        ∃(n, n ∈ N /\ declaration.constructorVarsInDomain(constructor, app(h)(n)))
    )
    val substitutions = Seq(A := recursive, payload := A, recursive := otherPayload, h := otherRecursive)
    val checked = Theorem.generated(schema.substitute(substitutions*)) {
      val before = lisa.SetTheoryLibrary.theorems.all.size
      val instance = declaration.termsHaveHeight(constructor, otherRecursive, substitutions)
      assert(lisa.SetTheoryLibrary.theorems.all.size == before)
      have(thesis) by Restate.from(instance)
    }
    assert(!checked.hasErrorsOrSorry)

  test("height witnesses stay distinct from fields and their indexed variants"):
    val A, heightWitness, stageWitness, payload = variable[Ind]
    val variables = Seq(h, Variable[Ind](Identifier("h", 1)), n, Variable[Ind](Identifier("n", 1)), m, Variable[Ind](Identifier("m", 1)))
    val alternatives = variables.indices.map(i => Variable[Ind](s"argument$i"))
    val name = "commonHeightFreshWitnesses"
    val constructor = new SyntacticConstructor(
      Seq(TypeArg("A")) ++ Seq.fill(variables.size - 1)(SelfRef),
      variables,
      alternatives,
      0,
      name
    )
    val declaration = new SyntacticADT(name, Seq(constructor), Seq(A))
    def fieldsIn(domain: Expr[Ind]): Expr[Prop] =
      declaration.constructorVarsInDomain(constructor, domain).substitute(h := payload)
    val checked = Theorem.generated(
      declaration.isHeight(heightWitness) |- (
        fieldsIn(declaration.term) <=> ∃(stageWitness, stageWitness ∈ N /\ fieldsIn(app(heightWitness)(stageWitness)))
      )
    ) {
      have(thesis) by Restate.from(declaration.termsHaveHeight(constructor, heightWitness, Seq(h := payload)))
    }
    assert(!checked.hasErrorsOrSorry && !declaration.intro(constructor).hasErrorsOrSorry)
