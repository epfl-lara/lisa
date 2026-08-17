package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * Shared support for **definitional naming**: creating a fresh naming predicate over a subformula's free
 * variables, and the small kernel proofs that discharge a naming definition `∀x̄. d(x̄) ⇔ subst`. Used by
 * [[SkolemPhase]] (ε-discharge), [[NamingPhase]] (certified selective naming),
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
  def proveQuantifiedReflIff(subst: Expression, freeVars: Seq[Variable]): SCProof =
    val implFormula = implies(subst)(subst)
    val base = IndexedSeq(
      Hypothesis(subst |- subst, subst),
      RightImplies(() |- implFormula, 0, subst, subst),
      RightIff(() |- (subst <=> subst), 1, 1, subst, subst))
    quantifyProof(base, subst <=> subst, freeVars)

  /**
    * The variables a naming atom over `f` abstracts: `f`'s free `Ind`-sorted variables, minus `frozen`, ordered
    * by identifier. `frozen` variables are excluded because they are considered uninterpreted "constants"
    * pinned by a defining equality.
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
  def freshNamingAtom(f: Expression, counter: Counter, frozen: Set[Variable]): (Variable, Seq[Variable], Expression) =
    freshNamingAtomOver(namingVars(f, frozen), counter)

  /** [[freshNamingAtom]] for a caller that already holds [[namingVars]]`(f, frozen)`, so the free-variable walk
    * is not repeated. [[NamingPhase]] is such a caller: it sized its marker from that same list. */
  def freshNamingAtomOver(freeVars: Seq[Variable], counter: Counter): (Variable, Seq[Variable], Expression) = {
    val nmId = Identifier(GeneratedNames.namingAtom, counter.next())
    val nmSort = freeVars.foldRight(Prop: Sort)((v, acc) => v.sort -> acc)
    val nm = Variable(nmId, nmSort)
    val nmApp = freeVars.foldLeft(nm: Expression)((acc, v) => acc(v))
    (nm, freeVars, nmApp)
  }
