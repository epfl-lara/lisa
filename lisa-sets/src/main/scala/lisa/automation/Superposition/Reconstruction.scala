package lisa.automation.superposition

import scala.collection.mutable

import lisa.utils.K

import Core.*

/**
 * Reconstruction of a refutation (the empty clause and its [[Justification]] DAG) into a Lisa kernel
 * [[lisa.utils.K.SCProof]] whose imports are the input clause-sequents and whose conclusion is the
 * empty sequent `⊢`. See `Reconstruction.md` for the design.
 *
 * Each clause becomes one proof reference (an import or a step), **memoised** by clause id so a clause
 * reused across the DAG is expanded once. Every clause's kernel sequent uses a per-clause canonical
 * variable naming (`reconV<id>`), so any two clauses are standardised apart. Inputs import the user's
 * exact sequent and a per-input `InstSchema` renames its variables to the canonical scheme.
 *
 * The mapping: `Input` → import (+ rename `InstSchema`); `Factoring` → `InstSchema` (the merged
 * literals collapse in the set-sequent); `Resolution` → `InstSchema` of each parent by the recomputed
 * mgu, then `Cut` on the resolved atom; `Canonicalization` → pass-through (sort/dedup are no-ops on
 * set-sequents). The mgu is recomputed by re-unifying the recorded literals; the conclusion's variable
 * numbering is recovered by replaying the inference's `Applier` over the surviving literals.
 *
 * Symbols are interned by their full identifier string ([[Bridge]] uses `id.toString`, which encodes
 * the counter index `id.no`), so a rebuilt symbol's identifier is recovered exactly via [[identOf]]
 * (e.g. `e_1` round-trips as `Identifier("e", 1)`, not the wrong `Identifier("e_1", 0)`).
 */
object Reconstruction:

  /** An input clause's original sequent plus the map (internal var number → its original kernel variable). */
  type InputInfo = (K.Sequent, Map[Int, K.Variable])

  /**
   * Reconstruct the refutation rooted at `empty` into a kernel proof. `inputs` maps each input clause's
   * id to its original sequent and variable map (supplied by [[Bridge]]).
   */
  def reconstruct(empty: Clause, bank: TermBank, inputs: collection.Map[Int, InputInfo]): K.SCProof =
    new Builder(bank, inputs).reconstructProof(empty)

  private final class Builder(bank: TermBank, inputs: collection.Map[Int, InputInfo]):
    private val sig: Signature = bank.signature
    private val steps: mutable.ArrayBuffer[K.SCProofStep] = mutable.ArrayBuffer.empty
    private val imports: mutable.ArrayBuffer[K.Sequent] = mutable.ArrayBuffer.empty
    private val memo: mutable.Map[Int, Recon] = mutable.Map.empty
    private val trail: Trail = new Trail(bank)

    def reconstructProof(empty: Clause): K.SCProof =
      refOf(empty)
      K.SCProof(steps.toIndexedSeq, imports.toIndexedSeq)

    /** A reconstructed clause: proof reference, kernel sequent, and its internal-var → kernel-var map. */
    private final case class Recon(ref: Int, seq: K.Sequent, vars: Int => K.Variable)

    private def addStep(s: K.SCProofStep): Int = { steps += s; steps.length - 1 }
    private def addImport(s: K.Sequent): Int = { imports += s; -imports.length }

    /** A globally-unique kernel variable for internal var `n` of clause `id` (standardises clauses apart). */
    private def canonVar(id: Int, n: Int): K.Variable = K.Variable(K.Identifier(s"reconV$id", n), K.Ind)

    private def refOf(c: Clause): Recon = memo.get(c.id) match
      case Some(r) => r
      case None =>
        val r = build(c)
        memo(c.id) = r
        r

    private def build(c: Clause): Recon = c.justification match
      case Justification.Input => buildInput(c)
      case Justification.Canonicalization(p) => refOf(p) // sort/dedup are no-ops on a set-sequent
      case Justification.Factoring(p, i, j) => buildFactoring(c, p, i, j)
      case Justification.Resolution(l, i, r, j) => buildResolution(c, l, i, r, j)

    private def buildInput(c: Clause): Recon =
      val (origSeq, vm) = inputs(c.id)
      val cv: Int => K.Variable = n => canonVar(c.id, n)
      val imp = addImport(origSeq)
      if vm.isEmpty then Recon(imp, origSeq, cv)
      else
        val subst: Map[K.Variable, K.Expression] = vm.map((n, ov) => ov -> (cv(n): K.Expression)).toMap
        val canonSeq = substSeq(origSeq, subst)
        Recon(addStep(K.InstSchema(canonSeq, imp, subst)), canonSeq, cv)

    private def buildFactoring(c: Clause, parent: Clause, i: Int, j: Int): Recon =
      val p = refOf(parent)
      val cv: Int => K.Variable = n => canonVar(c.id, n)
      val saved = trail.save()
      trail.unify(bank.atomOf(parent.literals(i)), 0, bank.atomOf(parent.literals(j)), 0)
      val applier = trail.applier()
      replaySurvivors(applier, parent, skip = j, scope = 0) // fix the conclusion's variable numbering
      val subst = substOf(parent, p.vars, applier, scope = 0, cv)
      val bot = substSeq(p.seq, subst)
      trail.restore(saved)
      if subst.isEmpty then Recon(p.ref, bot, cv)
      else Recon(addStep(K.InstSchema(bot, p.ref, subst)), bot, cv)

    private def buildResolution(c: Clause, left: Clause, i: Int, right: Clause, j: Int): Recon =
      val pl = refOf(left); val pr = refOf(right)
      val cv: Int => K.Variable = n => canonVar(c.id, n)
      val saved = trail.save()
      trail.unify(bank.atomOf(left.literals(i)), 0, bank.atomOf(right.literals(j)), 1)
      val applier = trail.applier()
      replaySurvivors(applier, left, skip = i, scope = 0)
      replaySurvivors(applier, right, skip = j, scope = 1)
      val substL = substOf(left, pl.vars, applier, scope = 0, cv)
      val substR = substOf(right, pr.vars, applier, scope = 1, cv)
      val botL = substSeq(pl.seq, substL)
      val botR = substSeq(pr.seq, substR)
      val phi = K.substituteVariables(kernelize(bank.atomOf(left.literals(i)), pl.vars), substL)
      trail.restore(saved)
      val (refL, seqL) = instStep(pl, substL, botL)
      val (refR, seqR) = instStep(pr, substR, botR)
      // the positive side carries φ on the right (Cut's t1); the negative side carries it on the left (t2)
      val (t1ref, t1seq, t2ref, t2seq) =
        if bank.isPositive(left.literals(i)) then (refL, seqL, refR, seqR) else (refR, seqR, refL, seqL)
      val resolvent = K.Sequent(t1seq.left ++ (t2seq.left - phi), (t1seq.right - phi) ++ t2seq.right)
      Recon(addStep(K.Cut(resolvent, t1ref, t2ref, phi)), resolvent, cv)

    /** Emit an `InstSchema` for a non-empty substitution, else reuse the premise directly (identity-σ). */
    private def instStep(p: Recon, subst: Map[K.Variable, K.Expression], bot: K.Sequent): (Int, K.Sequent) =
      if subst.isEmpty then (p.ref, p.seq) else (addStep(K.InstSchema(bot, p.ref, subst)), bot)

    /** Replay the `Applier` over the surviving literals (all but `skip`), in index order, so its fresh
     *  variable numbering matches the clause the prover generated. */
    private def replaySurvivors(applier: trail.Applier, c: Clause, skip: Int, scope: Scope): Unit =
      var k = 0
      while k < c.literals.length do
        if k != skip then applier.apply(bank.atomOf(c.literals(k)), scope)
        k += 1

    /** The kernel substitution instantiating `parent`'s variables (named by `pVars`) under the trail,
     *  with images renamed to clause `cv`'s canonical variables. */
    private def substOf(parent: Clause, pVars: Int => K.Variable, applier: trail.Applier, scope: Scope, cv: Int => K.Variable): Map[K.Variable, K.Expression] =
      varsOf(parent).iterator.map(v => pVars(v) -> kernelize(applier.apply(bank.mkVar(Core.Variable(v)), scope), cv)).toMap

    private def substSeq(s: K.Sequent, subst: Map[K.Variable, K.Expression]): K.Sequent =
      if subst.isEmpty then s
      else K.Sequent(s.left.map(K.substituteVariables(_, subst)), s.right.map(K.substituteVariables(_, subst)))

    /** Convert an internal term to a kernel expression, mapping internal variable numbers via `vars`. */
    private def kernelize(t: Term, vars: Int => K.Variable): K.Expression =
      if bank.isVar(t) then vars(bank.varNum(t).num)
      else
        val info: SymbolInfo = sig.info(bank.headSymbol(t))
        var e: K.Expression = K.Constant(identOf(info.name), sortFor(info.arity, info.isPredicate))
        val n = bank.arity(t)
        var k = 0
        while k < n do
          e = K.Application(e, kernelize(bank.arg(t, k), vars))
          k += 1
        e

    /** Parse an interned symbol name (a kernel `Identifier.toString`) back to the exact identifier,
     *  recovering a trailing counter index (`"e_1"` → `Identifier("e", 1)`). Inverse of the [[Bridge]]
     *  intern key, using the kernel's own `String`→`Identifier` conversion. */
    private def identOf(name: String): K.Identifier = K.given_Conversion_String_Identifier(name)

    /** The kernel sort of a symbol: `Ind → … → Ind → (Prop|Ind)` with `arity` argument places. */
    private def sortFor(arity: Int, isPredicate: Boolean): K.Sort =
      var s: K.Sort = if isPredicate then K.Prop else K.Ind
      var k = 0
      while k < arity do { s = K.Ind -> s; k += 1 }
      s

    private def varsOf(c: Clause): Set[Int] =
      val s = mutable.Set.empty[Int]
      c.literals.foreach(l => collectVars(bank.atomOf(l), s))
      s.toSet

    private def collectVars(t: Term, s: mutable.Set[Int]): Unit =
      if bank.isVar(t) then s += bank.varNum(t).num
      else
        val n = bank.arity(t)
        var k = 0
        while k < n do { collectVars(bank.arg(t, k), s); k += 1 }
