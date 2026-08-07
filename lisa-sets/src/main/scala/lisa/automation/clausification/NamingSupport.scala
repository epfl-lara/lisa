package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * Shared support for **definitional naming**: minting a fresh naming predicate over a subformula's free
 * variables, and the small kernel proofs that discharge a naming definition `∀x̄. d(x̄) ⇔ subst`. Used by
 * [[SkolemPhase]] (ε-discharge), [[CertifiedFastClausifier.certifyFastNaming]] (certified selective naming),
 * and the uncertified [[FastClausify]].
 */
private[clausification] object NamingSupport:

  /** `∀v_0...∀v_{n-1}. body` (innermost-first foldRight). */
  def quantifyAll(body: Expression, vars: Seq[Variable]): Expression =
    vars.foldRight(body)((v, acc) => forall(Lambda(v, acc)))

  /** `λv_0...λv_{n-1}. body` (innermost-first foldRight). */
  def lambdifyAll(body: Expression, vars: Seq[Variable]): Expression =
    vars.foldRight(body)((v, acc) => Lambda(v, acc))

  /** A reflexive quantified iff proof `() ⊢ ∀x̄. (subst ⇔ subst)` (Hypothesis → RightImplies → RightIff →
    * RightForall × |x̄|). Used to discharge a naming definition after its schema variable has been instantiated
    * to `λx̄. subst`. */
  def proveQuantifiedReflIff(subst: Expression, freeVars: Seq[Variable]): SCProof = {
    val n = freeVars.size
    val totalSteps = 3 + n
    val steps = new Array[SCProofStep](totalSteps)
    steps(0) = Hypothesis(subst |- subst, subst)
    val implFormula = implies(subst)(subst)
    steps(1) = RightImplies(() |- implFormula, 0, subst, subst)
    val iffFormula = subst <=> subst
    steps(2) = RightIff(() |- iffFormula, 1, 1, subst, subst)
    var body: Expression = iffFormula
    var ref = 2
    for (k <- 0 until n) {
      val v = freeVars(n - 1 - k)
      val phi = body
      body = forall(Lambda(v, body))
      steps(3 + k) = RightForall(() |- body, ref, phi, v)
      ref = 3 + k
    }
    SCProof(steps.toIndexedSeq, IndexedSeq.empty)
  }

  /** Build a fresh schematic naming atom over `f`'s free variables.
    *
    * Returns `(nm, freeVars, nmApp)` where:
    *   - `nm` is a fresh [[Variable]] (NOT a [[Constant]]) of sort `s_1 -> ... -> s_n -> Prop` so that
    *     [[InstSchema]] can later substitute it with a Lambda body.
    *   - `freeVars = [v_1, ..., v_n]` are the free variables of `f` in a fixed order.
    *   - `nmApp = nm(v_1)...(v_n)` is the application that replaces `f` in the rewritten formula.
    */
  def freshNamingAtom(f: Expression, counter: Counter, frozen: Set[Variable] = Set.empty): (Variable, Seq[Variable], Expression) = {
    // Only the Ind-sorted free variables are abstracted into `nm` — higher-sorted free variables (e.g. predicate
    // or function variables like `P : Ind → Prop`) cannot be `forall`-quantified by the kernel, so they remain
    // free in the iff/quantified definitional context (acting as opaque parameters). They are still substituted
    // correctly by [[InstSchema]] since `nm` is fresh and substituting it cannot capture any other free variable.
    // `frozen` variables (Skolem-function symbols from [[SkolemPhase]]) are excluded too: they are uninterpreted
    // constants pinned by a defining equality, so a nullary one (Ind-sorted) must NOT be ∀-closed here either.
    val freeVars = f.freeVariables.toSeq.filter(v => v.sort == Ind && !frozen.contains(v)).sortBy(_.id.toString)
    val nmId = Identifier(GeneratedNames.namingAtom, counter.next())
    val nmSort = freeVars.foldRight(Prop: Sort)((v, acc) => v.sort -> acc)
    val nm = Variable(nmId, nmSort)
    val nmApp = freeVars.foldLeft(nm: Expression)((acc, v) => acc(v))
    (nm, freeVars, nmApp)
  }
