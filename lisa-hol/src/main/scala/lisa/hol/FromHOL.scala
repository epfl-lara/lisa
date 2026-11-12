package lisa.hol

import lisa.hol.VarsAndFunctions._
import lisa.hol.basics.{Connectives => C}
import lisa.hol.basics.{Disjunction => D}
import lisa.hol.basics.{Exists => E}
import lisa.hol.basics.{False => F}
import lisa.hol.basics.{Forall => FA}
import lisa.hol.basics.{Truth => T}
import lisa.hol.{HOLHelperTheorems => H}
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.maths.SetTheory.Types.TypingRules
import lisa.utils.prooflib.Discharge
import lisa.utils.prooflib.Proof
import lisa.utils.prooflib.ProofJudgement
import lisa.utils.prooflib.Subproof
import lisa.utils.prooflib.Thm

/**
 * Translate the first-order spine using proved equivalences, without unfolding arbitrary HOL constants.
 */
object FromHOL extends lisa.Main:
  import HOLLogicalSymbols.{Logical, Symbol, symbol}
  import Symbol.*

  private val A, x, y = variable[Ind]

  /**
   * Translate Boolean formulas on both sides; leave unknown constants and higher-order arguments opaque.
   */
  def fromHOL(premise: Thm)(using sourcecode.File, sourcecode.Line): ProofJudgement = Subproof:
    val context = premise.left ++ getContext(premise.statement)
    val typing = context.filter:
      case TypeAssign(_, _) => true
      case ∃(bound, element ∈ _) if bound == element => true
      case _ => false

    def rewrite(current: Thm, original: Expr[Prop], left: Boolean): Thm = original match
      case eqOne(term) =>
        val (translated, equivalence) = boolean(term, typing, context)
        if translated == original then current
        else
          val target =
            if left then current.statement.copy(left = current.left - original + translated ++ equivalence.left)
            else current.statement.copy(left = current.left ++ equivalence.left, right = current.right - original + translated)
          val pivot = Variable.fresh[Prop](current.left ++ current.right ++ equivalence.left, "hol")
          if left then have(target) by LeftSubst.withParameters(Seq((original, translated, Nil)), Seq(pivot) -> pivot)(current, Seq(equivalence))
          else have(target) by RightSubst.withParameters(Seq((original, translated, Nil)), Seq(pivot) -> pivot)(current, Seq(equivalence))
      case _ => current

    val left = premise.left.foldLeft(premise)((current, formula) => rewrite(current, formula, left = true))
    val result = premise.right.foldLeft(left)((current, formula) => rewrite(current, formula, left = false))
    have(result)

  /**
   * Look up and translate an HOL theorem, propagating lookup failures from the store.
   */
  def fromHOL(name: String, store: String => Thm)(using sourcecode.File, sourcecode.Line): ProofJudgement =
    fromHOL(store(name))

  /**
   * Certify a Boolean formula's translation independently of any theorem using it.
   */
  private[hol] def equivalence(term: Expr[Ind], context: Set[Expr[Prop]]): ProofJudgement = Subproof:
    val (_, proof) = boolean(term, context, context + eqOne(term))
    have(proof)

  private def reflexive(formula: Expr[Prop])(using Proof): Thm =
    have(formula <=> formula) by Restate

  /**
   * Transport subformulas through their proved equivalences.
   */
  private def compose(source: Expr[Prop], base: Thm, pairs: Seq[(Expr[Prop], Expr[Prop], Thm)])(
      build: Seq[Expr[Prop]] => Expr[Prop]
  )(using Proof): Thm =
    val avoid = base.left ++ base.right ++ pairs.flatMap(pair => Seq(pair._1, pair._2))
    val variables = pairs.indices.foldLeft(Vector.empty[Variable[Prop]]): (variables, _) =>
      variables :+ Variable.fresh[Prop](avoid ++ variables, "hol")
    pairs.indices.foldLeft(base): (current, index) =>
      val (before, after, comparison) = pairs(index)
      val children = pairs.indices.map: j =>
        if j == index then variables(j) else if j < index then pairs(j)._2 else pairs(j)._1
      val body = source <=> build(children)
      val target = body.substitute(variables(index) := after)
      have((current.left ++ comparison.left) |- target) by
        RightSubst.withParameters(Seq((before, after, Nil)), Seq(variables(index)) -> body)(current, Seq(comparison))

  private def typed(term: Expr[Ind], typ: Expr[Ind], context: Set[Expr[Prop]])(using Proof): Thm =
    have(Typecheck.checkProof(using lisa.SetTheoryLibrary)(context ++ getContext(term), term, typ))

  /**
   * Discharge the binder's typing before generalizing the pointwise equivalence.
   */
  private def quantified(
      universal: Boolean,
      bound: Variable[Ind],
      domain: Expr[Ind],
      before: Expr[Prop],
      after: Expr[Prop],
      pointwise: Thm
  )(using Proof): Thm =
    val guard = bound ∈ domain
    val context = pointwise.left - guard
    def quantify(body: Expr[Prop]): Expr[Prop] =
      if universal then ∀(bound, guard ==> body) else ∃(bound, guard /\ body)

    def direction(source: Expr[Prop], target: Expr[Prop]): Thm =
      val implication = have((context + guard + source) |- target) by Weakening(pointwise)
      if universal then
        val instance = guard ==> source
        val guardProof = have((context + guard) |- guard) by Hypothesis.withParameters(guard)
        val applied = have((context + guard + instance) |- target) by
          LeftImplies.withParameters(guard, source)(guardProof, implication)
        val opened = have((context + guard + quantify(source)) |- target) by
          LeftForall.withParameters(instance, bound, bound)(applied)
        val guarded = have((context + quantify(source)) |- (guard ==> target)) by
          RightImplies.withParameters(guard, target)(opened)
        val closed = have((context + quantify(source)) |- quantify(target)) by
          RightForall.withParameters(guard ==> target, bound)(guarded)
        have(context |- (quantify(source) ==> quantify(target))) by
          RightImplies.withParameters(quantify(source), quantify(target))(closed)
      else
        val guardProof = have((context + guard + source) |- guard) by Hypothesis.withParameters(guard)
        val conjunction = have((context + guard + source) |- (guard /\ target)) by
          RightAnd.withParameters(Seq(guard, target))(Seq(guardProof.kernel, implication.kernel))
        val witnessed = have((context + guard + source) |- quantify(target)) by
          RightExists.withParameters(guard /\ target, bound, bound)(conjunction)
        val packed = have((context + (guard /\ source)) |- quantify(target)) by
          LeftAnd.withParameters(guard, source)(witnessed)
        val closed = have((context + quantify(source)) |- quantify(target)) by
          LeftExists.withParameters(guard /\ source, bound)(packed)
        have(context |- (quantify(source) ==> quantify(target))) by
          RightImplies.withParameters(quantify(source), quantify(target))(closed)

    val forward = direction(before, after)
    val backward = direction(after, before)
    have(context |- (quantify(before) <=> quantify(after))) by RightIff(forward, backward)

  private def boolean(term: Expr[Ind], context: Set[Expr[Prop]], avoid: Set[Expr[Prop]])(using Proof): (Expr[Prop], Thm) =
    val source = eqOne(term)
    def finish(target: Expr[Prop], proof: Thm): (Expr[Prop], Thm) =
      target -> (have(proof.left |- (source <=> target)) by Weakening(proof))
    def binary(left: Expr[Ind], right: Expr[Ind], rule: Thm)(build: (Expr[Prop], Expr[Prop]) => Expr[Prop]): (Expr[Prop], Thm) =
      val (newLeft, leftProof) = boolean(left, context, avoid)
      val (newRight, rightProof) = boolean(right, context, avoid)
      val aligned = have(Discharge(typed(left, H.𝔹, context), typed(right, H.𝔹, context))(rule))
      val proof = compose(source, aligned, Seq((eqOne(left), newLeft, leftProof), (eqOne(right), newRight, rightProof)))(parts => build(parts(0), parts(1)))
      build(newLeft, newRight) -> proof

    term match
      case Logical(Truth, Seq()) =>
        finish(⊤, if term == H.One then reflexive(source) else T.holTruth.thm)
      case Logical(Falsehood, Seq()) =>
        val zero = have((H.Zero === H.One) <=> ⊥) by Weakening(H.`0 != 1`)
        val proof = if term == H.Zero then zero else have((term === H.One) <=> ⊥) by Substitute(F.holFalseZero)(zero)
        finish(⊥, proof)
      case Sapp(Sapp(Logical(And, Seq()), left), right) =>
        binary(left, right, C.handCorrect.of(C.p := left, C.q := right))(_ /\ _)
      case Sapp(Sapp(Logical(Or, Seq()), left), right) =>
        binary(left, right, D.horCorrect.of(D.p := left, D.q := right))(_ \/ _)
      case Sapp(Sapp(Logical(Implies, Seq()), left), right) =>
        binary(left, right, C.himpCorrect.of(C.p := left, C.q := right))(_ ==> _)
      case Sapp(Logical(Not, Seq()), body) =>
        val (translated, bodyProof) = boolean(body, context, avoid)
        val correctness = have(Discharge(typed(body, H.𝔹, context))(C.hnotCorrect.of(C.p := body)))
        finish(!translated, compose(source, correctness, Seq((eqOne(body), translated, bodyProof)))(parts => !parts.head))
      case Sapp(Sapp(Logical(Equality, Seq(domain)), left), right) if symbol(domain).contains(Bool) =>
        binary(left, right, C.hiffCorrect.of(C.p := left, C.q := right))(_ <=> _)
      case Sapp(Sapp(Logical(Equality, Seq(domain: Expr[Ind] @unchecked)), left), right) =>
        val correctness = have(Discharge(typed(left, domain, context), typed(right, domain, context))(H.eqAlign.of(A := domain, x := left, y := right)))
        finish(left === right, correctness)
      case Sapp(Logical(quantifier @ (Forall | Exists), Seq(domain: Expr[Ind] @unchecked)), predicate) =>
        val identifier = predicate match
          case Sabs(_, Abs(bound, _)) => bound.id
          case _ => Identifier("x")
        val bound = Variable[Ind](identifier).freshRename(avoid ++ context ++ Set(source))
        val application = predicate * bound
        val (body, beta) = predicate match
          case Sabs(_, abstraction @ Abs(boundVariable, inner: Expr[Ind])) =>
            val body = inner.substitute(boundVariable := bound)
            val T, e2 = variable[Ind]
            val e = variable[Ind >>: Ind]
            val beta = TypingRules.BetaReduction.of(T := domain, e := abstraction, e2 := bound)
            body -> Some(beta)
          case _ => application -> None
        val (translated, bodyProof) = boolean(body, context + (bound ∈ domain), avoid ++ context + (bound ∈ domain))
        val pointwise = beta.fold(bodyProof): beta =>
          val pivot = Variable.fresh[Ind](bodyProof.left ++ Set(source, translated), "hol")
          val comparison = have(beta.left |- body === application) by Restate.from(beta)
          have((bodyProof.left ++ beta.left) |- (eqOne(application) <=> translated)) by
            RightSubst.withParameters(Seq((body, application, Nil)), Seq(pivot) -> (eqOne(pivot) <=> translated))(bodyProof, Seq(comparison))
        val lifted = quantified(quantifier == Forall, bound, domain, eqOne(application), translated, pointwise)
        val rule =
          if quantifier == Forall then FA.hforallCorrect.of(FA.A := domain, FA.P := predicate, FA.x := bound)
          else E.hexistsCorrect.of(E.A := domain, E.P := predicate, E.x := bound)
        val correctness = have(Discharge(typed(predicate, domain ->: H.𝔹, context), have(TypeNonEmptyProof(domain)))(rule))
        val originalBody = if quantifier == Forall then ∀(bound ∈ domain, eqOne(application)) else ∃(bound ∈ domain, eqOne(application))
        val target = if quantifier == Forall then TypedForall(bound, domain, translated) else TypedExists(bound, domain, translated)
        finish(target, compose(source, correctness, Seq((originalBody, target, lifted)))(_.head))
      case _ => source -> reflexive(source)
