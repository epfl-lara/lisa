package lisa.maths.SetTheory.Types.ADT.recursion

import lisa.maths.SetTheory.Base.CartesianProduct.×
import lisa.maths.SetTheory.Base.Comprehension.|
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.PatternMatching.proofs.CaseDefinedWitness
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.Clause
import lisa.maths.SetTheory.Types.ADT.support.DefinedSymbol
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.InstantiateForallSeq
import lisa.utils.prooflib.Thm

/**
 * The case-defined graph W(g), with g supplying the recursive calls.
 */
private[recursion] final class Witness(spec: FunSpec) {
  private val pairWitness = spec.proofVariable("pairWitness")
  private val witnessBound = spec.argType × spec.returnType
  private val caseMembership: Expr[Ind] => Expr[Prop] = spec.patternMatching.caseMembership
  private val witnessClass = new DefinedSymbol(
    name = s"${spec.functionName}/witness",
    parametersSeq = spec.typeVariablesSeq :+ spec.selfPlaceholder,
    body = { pairWitness ∈ witnessBound | caseMembership(pairWitness) }
  )

  /**
   * The graph's defining equality.
   */
  val witnessDef: Thm = witnessClass.definition

  /**
   * Instantiates the graph with a candidate recursive function.
   */
  def apply(g: Expr[Ind]): Expr[Ind] =
    witnessClass.term.substitute(spec.selfPlaceholder := g)

  /**
   * The typing assumption on the candidate recursive function.
   */
  val typingPremise: Expr[Prop] = spec.selfPlaceholder :: spec.typ

  private val basePatterns: Set[Clause[Expr[Ind]]] = spec.adt.constructors
    .filter(_.selfRefVariables2.isEmpty)
    .flatMap(spec.patternMatching.clausesFor)
    .toSet

  private val checkReturnType: Map[Clause[Expr[Ind]], Thm] =
    spec.cases.map { pattern =>
      val premises = if basePatterns.contains(pattern) then Set.empty[Expr[Prop]] else Set(typingPremise)
      pattern -> Lemma
        .generated((pattern.typingPremises ++ premises) |- (pattern.body :: spec.returnType)) {
          have(thesis) by Typecheck.prove(using lisa.SetTheoryLibrary, summon[Proof])
        }
        .thm
    }.toMap

  private lazy val witnessSemantics = new CaseDefinedWitness(
    adt = spec.adt,
    argType = spec.argType,
    patternMatching = spec.patternMatching,
    returnType = spec.returnType,
    typ = spec.typ,
    witness = witnessClass.term,
    witnessDef = witnessDef,
    witnessBound = witnessBound,
    pairWitness = pairWitness,
    caseMembership = caseMembership,
    checkReturnType = checkReturnType,
    contextPremises = Seq(typingPremise)
  )

  /**
   * The graph has the declared function type under the candidate's typing assumption.
   */
  lazy val witnessHasType: Theorem = witnessSemantics.witnessHasType

  /**
   * The graph satisfies the given case equation.
   */
  def witnessCase(pattern: Clause[Expr[Ind]]): Theorem = witnessSemantics.witnessCase(pattern)

  /**
   * An input provides a target inhabitant, by induction on the input ADT.
   */
  val targetInhabited: Theorem = {
    val point = spec.proofVariable("input")
    val value = spec.proofVariable("inhabitant")
    val inhabited = ∃(value, value :: spec.returnType)
    val predicate = λ(point, inhabited)

    Lemma.generated(∀(point, point :: spec.argType ==> inhabited)) {
      val cases = spec.adt.constructors.map { constructor =>
        val inductiveCase = constructor.inductiveCase.substitute(spec.typeSubstitutions*).substitute(P := predicate)
        have(inductiveCase) subproof {
          if constructor.selfRefVariables2.nonEmpty then
            // Any recursive argument supplies the same constant induction hypothesis.
            have(thesis) by Tautology
          else
            val patterns = spec.patternMatching.clausesFor(constructor)
            val vars = patterns.head.variables2.take(constructor.arity)
            val input = constructor.appliedTerm(vars).substitute(spec.typeSubstitutions*)
            val typing = constructor.semanticSignature(vars).map((v, t) => v :: t.substitute(spec.typeSubstitutions*))
            val branches = patterns.map { pattern =>
              val guard = pattern.branchSelectionBody(input)
              val branch = have((typing.toSet + guard) |- inhabited) subproof {
                have(pattern.freshTypingFormula |- pattern.bodyAtFreshVars2 :: spec.returnType) by Restate.from(
                  checkReturnType(pattern).of(pattern.binders.zip(pattern.variables2).map((from, to) => from := to)*)
                )
                thenHave(pattern.freshTypingFormula |- inhabited) by RightExists
                thenHave(thesis) by Tautology
              }
              val (selection, selected) = pattern.variables2.drop(pattern.arity).foldRight((guard, branch)) { case (v, (condition, fact)) =>
                val existential = ∃(v, condition)
                val lifted = have((typing.toSet + existential) |- inhabited) by LeftExists(fact)
                (existential, lifted)
              }
              have(typing.toSet |- selection ==> inhabited) by RightImplies.withParameters(selection, inhabited)(selected)
            }
            val alternatives = seqOr(patterns.map(_.branchSelectionDisjunct(input)))
            val selector = have((seqAnd(typing) /\ (input === input)) ==> alternatives) by
              InstantiateForallSeq(vars)(spec.patternMatching.branchSelectionFor(constructor, input))
            val combined = have(typing.toSet |- inhabited) by Tautology.from((selector +: branches)*)
            val abstracted = vars.zip(typing).foldRight(combined) { case ((v, assumption), fact) =>
              val implication = have((fact.statement -<? assumption).left |- assumption ==> fact.statement.right.head) by Restate.from(fact)
              have(implication.statement.left |- ∀(v, implication.statement.right.head)) by RightForall(implication)
            }
            have(thesis) by Restate.from(abstracted)
        }
      }
      have(thesis) by Tautology.from((cases :+ spec.adt.induction.of(spec.typeSubstitutions*).of(P := predicate))*)
    }
  }

  private val _ = witnessSemantics
}
