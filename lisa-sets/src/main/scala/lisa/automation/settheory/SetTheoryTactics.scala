package lisa.automation.settheory

import lisa.SetTheoryLibrary.{_, given}
import lisa.automation.Tautology
import lisa.automation.kernel.CommonTactics.ExistenceAndUniqueness
import lisa.fol.FOL.{_, given}
import lisa.kernel.proof.SequentCalculus as SCunique
import lisa.maths.Quantifiers
import lisa.maths.settheory.SetTheory
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.{_, given}
import lisa.prooflib.SimpleDeducedSteps.Restate
import lisa.prooflib.*
import lisa.utils.Printer
import lisa.utils.unification.UnificationUtils.FormulaSubstitution
import lisa.utils.unification.UnificationUtils.TermSubstitution
import lisa.utils.unification.UnificationUtils.matchFormula

object SetTheoryTactics {
  // var defs
  private val x = variable
  private val y = variable
  private val z = variable
  private val v = variable
  private val h = formulaVariable
  private val P = predicate[1]
  private val Q = predicate[1]
  private val schemPred = predicate[1]

  /**
   * Deduced Tactic --- Unique Comprehension
   *
   * Generates a unique existence proof. Given a set `x`, and a predicate `P(t,
   * x)`, comprehension postulates there is a set containing the elements `t` of
   * `x` satisfying `P(t, x)`, denoted `{t ∈ x | P(t, x)}`. This set is unique
   * by extensionality.
   *
   *    `() ⊢ ∃! z. ∀ t. t ∈ z ⇔ (t ∈ x ⋀ P(t, x))`
   *
   * @param originalSet the set to apply comprehension on
   * @param separationPredicate the predicate to use for comprehension `(Term =>
   * Term => Boolean)`
   * @return subproof for unique existence of the set defined by inputs
   *
   * @example
   * Generates a subproof for the unique existence of the set `{t ∈ x | t ∈ y}`:
   * {{{
   *    have(() |- existsOne(z, forall(t, in(t, z) <=> (in(t, x) /\ in(t, y))))) by UniqueComprehension(x, lambda(Seq(t, x), in(t, y)))
   * }}}
   * See [[setIntersection]] or [[relationDomain]] for more usage.
   */
  object UniqueComprehension extends ProofTactic {
    def apply(using
        proof: Proof,
        line: sourcecode.Line,
        file: sourcecode.File,
        om: OutputManager
    )(originalSet: Term, separationPredicate: LambdaTF[1])( // TODO dotty forgets that Term <:< LisaObject[Term]
        bot: Sequent
    ): proof.ProofTacticJudgement = {
      require(separationPredicate.bounds.length == 1) // separationPredicate takes two args
      given lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary
      // fresh variable names to avoid conflicts
      val botWithAssumptions = bot ++ (proof.getAssumptions |- ())
      val takenIDs = (botWithAssumptions.freeVariables ++ separationPredicate.body.freeVariables ++ originalSet.freeVariables).map(_.id)
      val t1 = Variable(freshId(takenIDs, x.id))
      val t2 = Variable(freshId(takenIDs, y.id))

      val prop = (in(t2, originalSet) /\ separationPredicate(t2)) // TODO (Seq(t2, originalSet)
      def fprop(z: Term) = forall(t2, in(t2, z) <=> prop)

      /**
       * Proof Summary:
       *
       * originalSet = x
       * separationPredicate = \t x -> P(t, x)
       *
       * have    () |- ∃  z. t ∈ z <=> (t ∈ x /\ P(t, x))                                    Comprehension Schema Instantiation
       * import  ∃ z. t ∈ z <=> (t ∈ x /\ P(t, x)) |- ∃! z. t ∈ z <=> (t ∈ x /\ P(t, x))     Unique by Extension [[uniqueByExtension]] Instantiation
       * have    () |- ∃! z. t ∈ z <=> (t ∈ x /\ P(t, x))                                    Cut
       */
      val sp = TacticSubproof { // TODO check if isInstanceOf first
        val existence = have(() |- exists(t1, fprop(t1))) by Weakening(comprehensionSchema of (z -> originalSet, φ -> separationPredicate))

        val existsToUnique = have(exists(t1, fprop(t1)) |- existsOne(t1, fprop(t1))) by Weakening(SetTheory.uniqueByExtension of schemPred -> lambda(t2, prop))

        // assumption elimination
        have(() |- existsOne(t1, fprop(t1))) by Cut(existence, existsToUnique)
      }

      // safely check, unwrap, and return the proof judgement
      unwrapTactic(sp)("Subproof for unique comprehension failed.")
    }

    /**
     * Similarly to [[UniqueComprehension]], generates a unique existence proof
     * but for a set comprehension that is not over some other set `x`. To do so,
     * A proof that the predicate `P(t)` implies membership to the set `x` must be
     * given. This then asserts the unique existence of the set `{t | P(t)}`. Useful
     * when a definition includes a redundant membership condition.
     *
     *    `P(t) ==> t ∈ x ⊢ ∃! z. ∀ t. t ∈ z ⇔ P(t)`
     *
     * @param originalSet the set to apply comprehension on
     * @param separationPredicate the predicate to use for comprehension `(Term =>
     * Term => Boolean)`
     * @param predicateImpliesInOriginalSet proof of the form `P(t) ==> t ∈ originalSet`
     * @return subproof for unique existence of the set defined by inputs
     *
     * @example
     * Generates a subproof for the unique existence of the set `{t | ∃x. x ∈ a ∧ t = {x}}`:
     * {{{
     *    val implicationProof = have(exists(x, in(x, a) /\ (t === singleton(x))) ==> in(t, union(cartesianProduct(a, a)))) subproof {
     *      // ...
     *    }
     *    have(() |- existsOne(z, forall(t, in(t, z) <=> exists(x, in(x, a) /\ (t === singleton(x)))))) by UniqueComprehension.fromOriginalSet(
     *      union(cartesianProduct(a, a)),
     *      lambda(t, exists(x, in(x, a) /\ (t === singleton(x)))),
     *      implicationProof
     *    )
     * }}}
     * See [[UniqueComprehension]] for more usage.
     */
    def fromOriginalSet(using
        proof: Proof,
        line: sourcecode.Line,
        file: sourcecode.File,
        om: OutputManager
    )(originalSet: Term, separationPredicate: LambdaTF[1], predicateImpliesInOriginalSet: proof.Fact)( // TODO dotty forgets that Term <:< LisaObject[Term]
        bot: Sequent
    ): proof.ProofTacticJudgement = {
      require(separationPredicate.bounds.length == 1)
      given lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary
      // fresh variable names to avoid conflicts
      val botWithAssumptions = bot ++ (proof.getAssumptions |- ())
      val takenIDs = (botWithAssumptions.freeVariables ++ separationPredicate.body.freeVariables ++ originalSet.freeVariables).map(_.id)
      val t1 = Variable(freshId(takenIDs, x.id))
      val t2 = Variable(freshId(takenIDs, y.id))

      val separationCondition = separationPredicate(t2)
      val targetDef = ∀(t2, in(t2, t1) <=> separationCondition)
      val comprehension = ∀(t2, in(t2, t1) <=> in(t2, originalSet) /\ separationCondition)

      // prepare predicateImpliesInOriginalSet for usage in a proof: rename variables
      val predicateImpliesInOriginalSetForm = separationCondition ==> in(t2, originalSet)
      val predicateImpliesInOriginalSetReady = matchFormula(
        separationCondition ==> in(t2, originalSet),
        predicateImpliesInOriginalSet.statement.right.head
      ) match
        case None =>
          return proof.InvalidProofTactic(s"Unable to unify `predicateImpliesInOriginalSet` with the expected form: ${predicateImpliesInOriginalSetForm}")
        case Some((formulaSubst, termSubst)) =>
          predicateImpliesInOriginalSet
            .of(formulaSubst.map((k, v) => SubstPair(k, v)).toSeq*)
            .of(termSubst.map((k, v) => SubstPair(k, v)).toSeq*)

      val sp = TacticSubproof {
        // get uniqueness with the redundant original set membership
        val uniq = have(∃!(t1, comprehension)) by UniqueComprehension(
          originalSet,
          lambda(t2, separationCondition)
        )

        // show that existence of the definition with the original set membership implies the
        // existence of the definition without the original set membership
        val transform = have(
          ∃(t1, comprehension) |- ∃(t1, targetDef)
        ) subproof {
          // derive equivalence between t ∈ x /\ P(t) and P(t) from `predicateImpliesInOriginalSet`
          val lhs = have(separationCondition ==> (in(t2, originalSet) /\ separationCondition)) by Tautology.from(predicateImpliesInOriginalSetReady)
          val rhs = have(separationCondition /\ in(t2, originalSet) ==> separationCondition) by Restate
          val subst = have(separationCondition <=> (in(t2, originalSet) /\ separationCondition)) by RightIff(lhs, rhs)

          // subtitute and introduce quantifiers
          have((in(t2, t1) <=> (in(t2, originalSet) /\ separationCondition)) |- in(t2, t1) <=> (in(t2, originalSet) /\ separationCondition)) by Hypothesis
          val cutRhs = thenHave(
            (in(t2, t1) <=> (in(t2, originalSet) /\ separationCondition), separationCondition <=> (in(t2, originalSet) /\ separationCondition)) |- in(t2, t1) <=> (separationCondition)
          ) by RightSubstIff.withParametersSimple(List((separationCondition, in(t2, originalSet) /\ separationCondition)), lambda(h, in(t2, t1) <=> h))
          have((in(t2, t1) <=> (in(t2, originalSet) /\ separationCondition)) |- in(t2, t1) <=> (separationCondition)) by Cut(subst, cutRhs)
          thenHave(∀(t2, in(t2, t1) <=> (in(t2, originalSet) /\ separationCondition)) |- in(t2, t1) <=> (separationCondition)) by LeftForall
          thenHave(∀(t2, in(t2, t1) <=> (in(t2, originalSet) /\ separationCondition)) |- ∀(t2, in(t2, t1) <=> (separationCondition))) by RightForall
          thenHave(∀(t2, in(t2, t1) <=> (in(t2, originalSet) /\ separationCondition)) |- ∃(t1, ∀(t2, in(t2, t1) <=> (separationCondition)))) by RightExists
          thenHave(thesis) by LeftExists
        }

        val cutL = have(
          ∃!(t1, comprehension) |- ∃(t1, comprehension)
        ) by Restate.from(Quantifiers.existsOneImpliesExists of (P -> lambda(t1, comprehension)))
        val cutR = have(∃(t1, targetDef) |- ∃!(t1, targetDef)) by Restate.from(
          SetTheory.uniqueByExtension of (schemPred -> lambda(t2, separationCondition))
        )

        val trL = have(∃!(t1, comprehension) |- ∃(t1, targetDef)) by Cut(cutL, transform)
        val trR = have(∃!(t1, comprehension) |- ∃!(t1, targetDef)) by Cut(trL, cutR)
        have(∃!(t1, targetDef)) by Cut.withParameters(∃!(t1, comprehension))(uniq, trR)
      }

      // safely check, unwrap, and return the proof judgement
      unwrapTactic(sp)("Subproof for unique comprehension failed.")
    }
  }

  /**
   * Defines the element that is uniquely given by the uniqueness theorem, or falls back to the error element if the
   * assumptions of the theorem are not satisfied.
   *
   * This is useful in defining specific elements in groups, where their uniqueness (and existence) strongly rely
   * on the assumption of the group structure.
   */
  object TheConditional {
    def apply(using om: OutputManager)(u: Variable, f: Formula)(just: JUSTIFICATION, defaultValue: Term = ∅): The = {
      val seq = just.statement

      if (seq.left.isEmpty) {
        The(u, f)(just)
      } else {
        val prem = if (seq.left.size == 1) seq.left.head else And(seq.left.toSeq)
        val completeDef = (prem ==> f) /\ (!prem ==> (u === defaultValue))
        val substF = completeDef.substitute(u := defaultValue)
        val substDef = completeDef.substitute(u := v)

        val completeUniquenessTheorem = Lemma(
          ∃!(u, completeDef)
        ) {
          val case1 = have(prem |- ∃!(u, completeDef)) subproof {
            // We prove the equivalence f <=> completeDef so that we can substitute it in the uniqueness quantifier
            val equiv = have(prem |- ∀(u, f <=> completeDef)) subproof {
              have(f |- f) by Hypothesis
              thenHave((prem, f) |- f) by Weakening
              val left = thenHave(f |- (prem ==> f)) by Restate

              have(prem |- prem) by Hypothesis
              thenHave((prem, !prem) |- ()) by LeftNot
              thenHave((prem, !prem) |- (u === defaultValue)) by Weakening
              val right = thenHave(prem |- (!prem ==> (u === defaultValue))) by Restate

              have((prem, f) |- completeDef) by RightAnd(left, right)
              val forward = thenHave(prem |- f ==> completeDef) by Restate

              have(completeDef |- completeDef) by Hypothesis
              thenHave((prem, completeDef) |- completeDef) by Weakening
              thenHave((prem, completeDef) |- f) by Tautology
              val backward = thenHave(prem |- completeDef ==> f) by Restate

              have(prem |- f <=> completeDef) by RightIff(forward, backward)
              thenHave(thesis) by RightForall
            }

            val substitution = have((∃!(u, f), ∀(u, f <=> completeDef)) |- ∃!(u, completeDef)) by Tautology.from(
              Quantifiers.uniqueExistentialEquivalenceDistribution of (P := lambda(u, f), Q := lambda(u, completeDef))
            )

            val implication = have((prem, ∃!(u, f)) |- ∃!(u, completeDef)) by Cut(equiv, substitution)
            val uniqueness = have(prem |- ∃!(u, f)) by Restate.from(just)
            have(prem |- ∃!(u, completeDef)) by Cut(uniqueness, implication)
          }

          val case2 = have(!prem |- ∃!(u, completeDef)) subproof {
            val existence = have(!prem |- ∃(u, completeDef)) subproof {
              have(!prem |- !prem) by Hypothesis
              thenHave((prem, !prem) |- ()) by LeftNot
              thenHave((prem, !prem) |- substF) by Weakening
              val left = thenHave(!prem |- (prem ==> substF)) by Restate

              have(defaultValue === defaultValue) by RightRefl
              thenHave(!prem |- defaultValue === defaultValue) by Weakening
              val right = thenHave(!prem ==> (defaultValue === defaultValue)) by Restate

              have(!prem |- (prem ==> substF) /\ (!prem ==> (defaultValue === defaultValue))) by RightAnd(left, right)
              thenHave(thesis) by RightExists.withParameters(defaultValue)
            }

            val uniqueness = have((!prem, completeDef, substDef) |- (u === v)) subproof {
              assume(!prem)
              assume(completeDef)
              assume(substDef)

              val eq1 = have(u === defaultValue) by Tautology
              val eq2 = have(defaultValue === v) by Tautology
              val p = have((u === defaultValue) /\ (defaultValue === v)) by RightAnd(eq1, eq2)

              val transitivity = Quantifiers.equalityTransitivity of (x -> u, y -> defaultValue, z -> v)
              have(thesis) by Cut(p, transitivity)
            }

            have(thesis) by ExistenceAndUniqueness(completeDef)(existence, uniqueness)
          }

          have(thesis) by Tautology.from(case1, case2)
        }

        The(u, completeDef)(completeUniquenessTheorem)
      }
    }
  }

}
