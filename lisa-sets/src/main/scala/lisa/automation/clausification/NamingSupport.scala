package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * Shared support for **definitional naming**: minting a fresh naming predicate over a subformula's free
 * variables, and the small kernel proofs that discharge a naming definition `∀x̄. d(x̄) ⇔ subst`. Used by
 * [[SkolemPhase]] (ε-discharge), [[CertifiedClausifier.certifyNaming]] (certified selective naming),
 * and the uncertified [[UncertifiedClausifier]].
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

  /**
    * The variables a naming atom over `f` abstracts: `f`'s free `Ind`-sorted variables, minus `frozen`, ordered by
    * identifier.
    *
    * Higher-sorted free variables (a predicate variable `P : Ind → Prop`, say) are excluded because the kernel
    * cannot `forall`-quantify them; they stay free in the definition as opaque parameters, and [[InstSchema]] still
    * substitutes them correctly since `nm` is fresh and cannot capture. `frozen` variables are excluded because
    * they are uninterpreted constants pinned by a defining equality. A *nullary* one is the only kind that needs
    * saying so: it is `Ind`-sorted, so the sort filter alone would abstract it, giving the atom an extra argument
    * that is the same constant at every occurrence and a definition that quantifies over a symbol not meant to vary.
    *
    * '''This is the single definition of that list.''' [[freshNamingAtom]] builds the atom's sort and application
    * from it, and `CertifiedClausifier.findSite` sizes its rewrite marker `p` from it. `nameOne` then
    * substitutes `p -> nm` directly, which is well-sorted only if the two lists agree exactly. They were two copies
    * of one filter expression; sharing this function is what makes the agreement structural rather than a comment.
    */
  def namingVars(f: Expression, frozen: Set[Variable]): Seq[Variable] =
    f.freeVariables.toSeq.filter(v => v.sort == Ind && !frozen.contains(v)).sortBy(_.id.toString)

  /** Build a fresh schematic naming atom over [[namingVars]]`(f, frozen)`.
    *
    * Returns `(nm, freeVars, nmApp)` where:
    *   - `nm` is a fresh [[Variable]] (NOT a [[Constant]]) of sort `s_1 -> ... -> s_n -> Prop` so that
    *     [[InstSchema]] can later substitute it with a Lambda body.
    *   - `freeVars = [v_1, ..., v_n]` is [[namingVars]]`(f, frozen)`.
    *   - `nmApp = nm(v_1)...(v_n)` is the application that replaces `f` in the rewritten formula.
    *
    * `frozen` has no default: every call site states what it is naming under, so the parameter cannot go quietly
    * unused again.
    */
  def freshNamingAtom(f: Expression, counter: Counter, frozen: Set[Variable]): (Variable, Seq[Variable], Expression) = {
    val freeVars = namingVars(f, frozen)
    val nmId = Identifier(GeneratedNames.namingAtom, counter.next())
    val nmSort = freeVars.foldRight(Prop: Sort)((v, acc) => v.sort -> acc)
    val nm = Variable(nmId, nmSort)
    val nmApp = freeVars.foldLeft(nm: Expression)((acc, v) => acc(v))
    (nm, freeVars, nmApp)
  }
