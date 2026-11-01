package lisa.hol.basics

import lisa.hol.{FromHOL, HOLLogicalSymbols}
import lisa.hol.HOLHelperTheorems.*
import lisa.hol.HOLSteps.HOLProofType
import lisa.hol.VarsAndFunctions.*
import lisa.hol.basics.Connectives.himp
import lisa.hol.basics.Forall.hforall
import lisa.maths.SetTheory.Types.TypingHelpers.{fun as _, *, given}
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction
import lisa.utils.prooflib.{Discharge, Thm}

/** Define HOL Light disjunction and relate its Boolean elimination rule to native disjunction. */
object Disjunction extends lisa.HOL:
  val p, q = typedvar(𝔹)
  private val r = typedvar(𝔹)
  private val body = hforall(𝔹) * fun(r, himp * (himp * p * r) * (himp * (himp * q * r) * r))
  private val expression = fun(p, fun(q, body))

  val hor: HOLPolymorphicConstant[Ind] =
    val hor = DEF(expression)
    val typing = Theorem(hor :: (𝔹 ->: 𝔹 ->: 𝔹)):
      val typed = have(HOLProofType(expression))
      have(thesis) by Substitute(hor.definition)(typed)
    HOLLogicalSymbols.register(HOLLogicalSymbols.Symbol.Or,
      HOLPolymorphicConstant[Ind](hor.id, FunctionalClass(Nil, Nil, 𝔹 ->: 𝔹 ->: 𝔹), typing))

  val horCorrect = HOLTheorem((hor * p * q === One) <=> ((p === One) \/ (q === One))):
    assumeAll
    val left = p === One
    val right = q === One
    val truth = r === One
    val clause = (left ==> truth) ==> ((right ==> truth) ==> truth)
    val quantified = ∀(r ∈ 𝔹, clause)
    val disjunction = left \/ right

    // Expand the HOL binders and implications before proving the elimination rule.
    val expanded = have((body === One) <=> quantified) by
      Weakening(have(FromHOL.equivalence(body, Set(p ∈ 𝔹, q ∈ 𝔹))))
    val all = have(quantified |- quantified) by Hypothesis.withParameters(quantified)
    val atZero = have(quantified |- ((Zero ∈ 𝔹) ==> clause.substitute(r := Zero))) by InstantiateForall(Zero)(all)
    val applied = have((quantified, Zero ∈ 𝔹) |- clause.substitute(r := Zero)) by Restate.from(atZero)
    val conditional = have(Discharge(Zero.justif)(applied))
    val withFalse = have((quantified, !(Zero === One)) |- disjunction) by Weakening(conditional)
    val forwardBody = have(Discharge(`0 != 1`)(withFalse))
    val forward = have(quantified ==> disjunction) by RightImplies.withParameters(quantified, disjunction)(forwardBody)

    def branch(hypothesis: Expr[Prop]): Thm =
      val assumption = have(hypothesis |- hypothesis) by Hypothesis.withParameters(hypothesis)
      val consequence = have(truth |- truth) by Hypothesis.withParameters(truth)
      val elimination = have((hypothesis, hypothesis ==> truth) |- truth) by
        LeftImplies.withParameters(hypothesis, truth)(assumption, consequence)
      val weakened = have((hypothesis, left ==> truth, right ==> truth) |- truth) by Weakening(elimination)
      val inner = have((hypothesis, left ==> truth) |- ((right ==> truth) ==> truth)) by
        RightImplies.withParameters(right ==> truth, truth)(weakened)
      have(hypothesis |- clause) by RightImplies.withParameters(left ==> truth, (right ==> truth) ==> truth)(inner)

    val cases = have(disjunction |- clause) by
      LeftOr.withParameters(Seq(left, right))(Seq(branch(left).kernel, branch(right).kernel))
    val guarded = have(disjunction |- ((r ∈ 𝔹) ==> clause)) by Weakening(cases)
    val closed = have(disjunction |- quantified) by RightForall.withParameters((r ∈ 𝔹) ==> clause, r)(guarded)
    val backward = have(disjunction ==> quantified) by RightImplies.withParameters(disjunction, quantified)(closed)
    val native = have(quantified <=> disjunction) by RightIff(forward, backward)
    val proposition = variable[Prop]
    val translated = have((quantified <=> disjunction) |- ((body === One) <=> disjunction)) by
      RightSubstIff.withParameters(Seq(quantified -> disjunction), Seq(proposition) -> ((body === One) <=> proposition))(expanded)
    val aligned = have(Discharge(native)(translated))

    // Replay the two set-theoretic beta reductions of the defining lambda.
    val T, e2 = variable[Ind]
    val e = variable[Ind >>: Ind]
    val innerBeta = BetaReduction of (T := 𝔹, e := λ(q, body), e2 := q)
    val outerBeta = BetaReduction of (T := 𝔹, e := λ(p, fun(q, body)), e2 := p)
    have(body === body) by RightRefl
    thenHave((fun(q, body) * q) === body) by Substitute(innerBeta)
    thenHave((expression * p * q) === body) by Substitute(outerBeta)
    val unfolded = thenHave((hor * p * q) === body) by Substitute(hor.definition)
    have(thesis) by Substitute(unfolded)(aligned)
