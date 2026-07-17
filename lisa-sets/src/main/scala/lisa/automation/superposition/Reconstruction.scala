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
   * id to its original sequent and variable map (supplied by [[Bridge]]). `schematicNames` are the interned
   * symbol names that came from **schematic function variables** (Phase-3 abstraction of non-first-order
   * subterms); they are rebuilt as kernel `Variable`s rather than `Constant`s so a later `InstSchema` can
   * instantiate them back.
   */
  def reconstruct(
      empty: Clause,
      bank: TermBank,
      inputs: collection.Map[Int, InputInfo],
      schematicNames: Set[String] = Set.empty,
      discharge: Map[K.Variable, K.Expression] = Map.empty
  ): K.SCProof =
    new Builder(bank, inputs, schematicNames, discharge).reconstructProof(empty)

  private final class Builder(bank: TermBank, inputs: collection.Map[Int, InputInfo], schematicNames: Set[String], discharge: Map[K.Variable, K.Expression]):
    private val sig: Signature = bank.signature
    private val steps: mutable.ArrayBuffer[K.SCProofStep] = mutable.ArrayBuffer.empty
    private val imports: mutable.ArrayBuffer[K.Sequent] = mutable.ArrayBuffer.empty
    private val memo: mutable.Map[Int, Recon] = mutable.Map.empty
    private val trail: Trail = new Trail(bank)
    // Phase-3 abstraction discharge, keyed by interned symbol name for [[kernelize]]: each schematic function
    // symbol `F` maps to its closed value `λfv. e` (the original non-first-order subterm), inlined so the
    // rebuilt proof is purely `e`-bearing (no `F`, no trailing `InstSchema`). Empty for ordinary clausal input.
    private val dischargeByName: Map[String, K.Expression] = discharge.map((v, e) => v.id.toString -> e).toMap

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
      case Justification.Superposition(from, fi, fs, into, ii, pos) => buildSuperposition(c, from, fi, fs, into, ii, pos)
      case Justification.Demodulation(target, ti, pos, rule, rs) => buildDemodulation(c, target, ti, pos, rule, rs)
      case Justification.EqualityResolution(p, i) => buildEqualityResolution(c, p, i)
      case Justification.EqualityFactoring(p, d, ds, k, ks) => buildEqualityFactoring(c, p, d, ds, k, ks)

    /** Inline the Phase-3 discharge into a sequent: substitute every schematic `F` by its `λfv. e` value and
     *  β-normalise, turning `F`-bearing atoms into `e`-bearing ones. Identity when nothing was abstracted. */
    private def dischargeSeq(s: K.Sequent): K.Sequent =
      if discharge.isEmpty then s
      else K.Sequent(s.left.map(e => K.substituteVariables(e, discharge).betaNormalForm), s.right.map(e => K.substituteVariables(e, discharge).betaNormalForm))

    private def buildInput(c: Clause): Recon =
      val (rawOrigSeq, vm) = inputs(c.id)
      val origSeq = dischargeSeq(rawOrigSeq) // present the import with `F` inlined back to its ε-term
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

    // --- equality inferences (Phase 4 Step 5) ------------------------------------------------------
    //
    // Superposition and demodulation share one shape ([[buildRewrite]]): instantiate both parents by the
    // recomputed unifier/matcher, `SubstEq` the rewritten literal in the *into/target* instance (adding the
    // equation `l=r` to its antecedent), then `Cut` the *from/rule* instance (carrying `l=r` on the right)
    // against it. Equality resolution collapses a unified disequality `s≉t` with `LeftRefl`; equality
    // factoring is a single `RightSubstEq` (plus a reorientation when the two equalities' sides disagree).

    private def buildSuperposition(c: Clause, from: Clause, iFrom: Int, fromSide: Int, into: Clause, iInto: Int, pos: Array[Int]): Recon =
      val fromAtom = bank.atomOf(from.literals(iFrom))
      val l = bank.arg(fromAtom, fromSide)
      buildRewrite(
        c, from, iFrom, fromSide, into, iInto, pos,
        establish = () => { trail.unify(l, 0, Superposition.subtermAt(bank, bank.atomOf(into.literals(iInto)), pos), 1); () },
        replay = ap =>
          // reproduce [[Superposition.superpose]]'s applier order so the conclusion's fresh var numbering matches `c`
          ap.apply(l, 0); ap.apply(bank.arg(fromAtom, 1 - fromSide), 0); ap.apply(bank.atomOf(into.literals(iInto)), 1)
          var k = 0
          while k < into.literals.length do { ap.apply(bank.atomOf(into.literals(k)), 1); k += 1 }
          k = 0
          while k < from.literals.length do { ap.apply(bank.atomOf(from.literals(k)), 0); k += 1 }
      )

    private def buildDemodulation(c: Clause, target: Clause, iTarget: Int, pos: Array[Int], rule: Clause, ruleSide: Int): Recon =
      val ruleAtom = bank.atomOf(rule.literals(0)) // the demodulator is a positive unit equality
      val l = bank.arg(ruleAtom, ruleSide)
      buildRewrite(
        c, rule, 0, ruleSide, target, iTarget, pos,
        establish = () => { trail.matchTerm(l, 0, Superposition.subtermAt(bank, bank.atomOf(target.literals(iTarget)), pos), 1); () },
        replay = ap =>
          // reproduce [[Demodulation.tryRewrite]]'s applier order (rule sides first, then target literals in order)
          ap.apply(l, 0); ap.apply(bank.arg(ruleAtom, 1 - ruleSide), 0)
          var k = 0
          while k < target.literals.length do { ap.apply(bank.atomOf(target.literals(k)), 1); k += 1 }
      )

    /**
     * The common superposition/demodulation reconstruction: `from` (scope 0) rewrites `into`'s literal `iInto`
     * at subterm `pos` with the equation on `from`'s side `fromSide`. `establish` re-binds the trail with the
     * unifier (superposition) or matcher (demodulation); `replay` re-runs the [[Trail.Applier]] in the
     * generating code's order so the conclusion's fresh variables match `c`. Emits a `SubstEq` (Right if the
     * rewritten literal is positive, else Left) that adds `lσ=rσ` to the antecedent, then a `Cut` on `lσ=rσ`.
     */
    private def buildRewrite(
        c: Clause, from: Clause, iFrom: Int, fromSide: Int, into: Clause, iInto: Int, pos: Array[Int],
        establish: () => Unit, replay: trail.Applier => Unit): Recon =
      val pFrom = refOf(from); val pInto = refOf(into)
      val cv: Int => K.Variable = n => canonVar(c.id, n)
      val fromAtom = bank.atomOf(from.literals(iFrom))
      val intoLit = into.literals(iInto)
      val intoAtom = bank.atomOf(intoLit)
      val saved = trail.save()
      establish()
      val applier = trail.applier()
      replay(applier)
      val substFrom = substOf(from, pFrom.vars, applier, scope = 0, cv)
      val substInto = substOf(into, pInto.vars, applier, scope = 1, cv)
      val botFrom = substSeq(pFrom.seq, substFrom)
      val botInto = substSeq(pInto.seq, substInto)
      // the equation's two stored sides (a0=a1 on `from`'s right) and the rewrite's occurrence sK → replacement tK
      val a0 = K.substituteVariables(kernelize(bank.arg(fromAtom, 0), pFrom.vars), substFrom)
      val a1 = K.substituteVariables(kernelize(bank.arg(fromAtom, 1), pFrom.vars), substFrom)
      val sK = K.substituteVariables(kernelize(Superposition.subtermAt(bank, intoAtom, pos), pInto.vars), substInto)
      val tK = K.substituteVariables(kernelize(bank.arg(fromAtom, 1 - fromSide), pFrom.vars), substFrom)
      val hole = freshHole()
      val phiBody = K.substituteVariables(kernelizeHole(intoAtom, pInto.vars, pos, 0, hole), substInto)
      val phiOfS = K.substituteVariables(phiBody, Map(hole -> sK)) // the into-literal's atom instance (φ(s))
      val phiOfT = K.substituteVariables(phiBody, Map(hole -> tK)) // the rewritten atom (φ(t))
      val eq = mkEqK(sK, tK) // lifted equation the SubstEq adds to the antecedent / the Cut resolves on
      trail.restore(saved)
      val (refInto, seqInto) = instStep(pInto, substInto, botInto)
      val (refFrom0, seqFrom0) = instStep(pFrom, substFrom, botFrom)
      // orient the `from` instance's equation to `sK=tK` (its stored order is a0=a1; flip when rewriting side 1)
      val (refFrom, seqFrom) = if fromSide == 0 then (refFrom0, seqFrom0) else flipEqRight(refFrom0, seqFrom0, a0, a1)
      val (refSubst, seqSubst) =
        if bank.isPositive(intoLit) then
          val bot = K.Sequent(seqInto.left + eq, (seqInto.right - phiOfS) + phiOfT)
          (addStep(K.RightSubstEq(bot, refInto, Seq((sK, tK)), (Seq(hole), phiBody))), bot)
        else
          val bot = K.Sequent((seqInto.left - phiOfS) + eq + phiOfT, seqInto.right)
          (addStep(K.LeftSubstEq(bot, refInto, Seq((sK, tK)), (Seq(hole), phiBody))), bot)
      val concl = K.Sequent(seqFrom.left ++ (seqSubst.left - eq), (seqFrom.right - eq) ++ seqSubst.right)
      Recon(addStep(K.Cut(concl, refFrom, refSubst, eq)), concl, cv)

    private def buildEqualityResolution(c: Clause, parent: Clause, i: Int): Recon =
      val pC = refOf(parent)
      val cv: Int => K.Variable = n => canonVar(c.id, n)
      val atom = bank.atomOf(parent.literals(i)) // the negative equality s ≉ t
      val saved = trail.save()
      trail.unify(bank.arg(atom, 0), 0, bank.arg(atom, 1), 0)
      val applier = trail.applier()
      replaySurvivors(applier, parent, skip = i, scope = 0)
      val substC = substOf(parent, pC.vars, applier, scope = 0, cv)
      val botC = substSeq(pC.seq, substC)
      val refl = K.substituteVariables(kernelize(atom, pC.vars), substC) // sσ = sσ, reflexive after unification
      trail.restore(saved)
      val (refC, seqC) = instStep(pC, substC, botC)
      val concl = K.Sequent(seqC.left - refl, seqC.right)
      Recon(addStep(K.LeftRefl(concl, refC, refl)), concl, cv)

    private def buildEqualityFactoring(c: Clause, parent: Clause, i: Int, iSide: Int, j: Int, jSide: Int): Recon =
      val pC = refOf(parent)
      val cv: Int => K.Variable = n => canonVar(c.id, n)
      val atomI = bank.atomOf(parent.literals(i)) // dropped equality s ≈ t (factored side iSide = s)
      val s = bank.arg(atomI, iSide); val t = bank.arg(atomI, 1 - iSide)
      val tp = bank.arg(bank.atomOf(parent.literals(j)), 1 - jSide) // partner's other side t'
      val saved = trail.save()
      trail.unify(s, 0, bank.arg(bank.atomOf(parent.literals(j)), jSide), 0) // σ = mgu(s, s')
      val applier = trail.applier()
      // reproduce [[Superposition.factorOne]]'s applier order (s, t, t', then the survivors, skipping i)
      applier.apply(s, 0); applier.apply(t, 0); applier.apply(tp, 0)
      replaySurvivors(applier, parent, skip = i, scope = 0)
      val substC = substOf(parent, pC.vars, applier, scope = 0, cv)
      val botC = substSeq(pC.seq, substC)
      val hole = freshHole()
      val phiBody = K.substituteVariables(kernelizeHole(atomI, pC.vars, Array(1 - iSide), 0, hole), substC)
      val tK = K.substituteVariables(kernelize(t, pC.vars), substC) // tσ
      val tpK = K.substituteVariables(kernelize(tp, pC.vars), substC) // t'σ
      val pK = K.substituteVariables(kernelize(s, pC.vars), substC) // sσ = s'σ (the shared maximal side)
      val phiOfS = K.substituteVariables(phiBody, Map(hole -> tK)) // literal i's atom instance (φ(s))
      val phiOfT = K.substituteVariables(phiBody, Map(hole -> tpK)) // the rewritten atom (φ(t)) in atom i's side order
      val eq = mkEqK(tK, tpK) // the introduced disequality's atom tσ = t'σ (added to the antecedent)
      trail.restore(saved)
      val (refC, seqC) = instStep(pC, substC, botC)
      // rewrite literal i (P≈tσ, on the right) to P≈t'σ using tσ=t'σ; adds tσ≠t'σ to the left (the new negative literal)
      val bot1 = K.Sequent(seqC.left + eq, (seqC.right - phiOfS) + phiOfT)
      val step1 = addStep(K.RightSubstEq(bot1, refC, Seq((tK, tpK)), (Seq(hole), phiBody)))
      // φ(t) came out in literal i's side order; if the kept partner j stores the reverse order, reorient it to merge
      if iSide == jSide then Recon(step1, bot1, cv)
      else
        val (fa, fb) = if iSide == 0 then (pK, tpK) else (tpK, pK) // the two sides of φ(t), stored order
        val (step2, bot2) = flipEqRight(step1, bot1, fa, fb)
        Recon(step2, bot2, cv)

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
        val n = bank.arity(t)
        val args: IndexedSeq[K.Expression] = (0 until n).map(k => kernelize(bank.arg(t, k), vars))
        applySymbol(bank.headSymbol(t), args)

    /** Apply interned symbol `head` to already-kernelised `args`, honouring Phase-3 discharge (inline a
     *  schematic `F` to its `λfv. e` value, β-reduced) and the schematic-symbol convention (an undischarged
     *  schematic symbol round-trips as a `Variable`, so a later `InstSchema` can target it). */
    private def applySymbol(head: Symbol, args: IndexedSeq[K.Expression]): K.Expression =
      val info: SymbolInfo = sig.info(head)
      dischargeByName.get(info.name) match
        case Some(lam) => args.foldLeft(lam)((acc, a) => K.Application(acc, a)).betaNormalForm
        case None =>
          val id: K.Identifier = identOf(info.name)
          val sort: K.Sort = sortFor(info.arity, info.isPredicate)
          val hd: K.Expression = if schematicNames.contains(info.name) then K.Variable(id, sort) else K.Constant(id, sort)
          args.foldLeft(hd)((acc, a) => K.Application(acc, a))

    /** Kernelise `t` but emit `hole` in place of the subterm at position `pos` (a path of argument indices),
     *  yielding a context `φ(hole)`; everything off the path is kernelised normally via [[kernelize]]. */
    private def kernelizeHole(t: Term, vars: Int => K.Variable, pos: Array[Int], depth: Int, hole: K.Variable): K.Expression =
      if depth == pos.length then hole
      else
        val n: Int = bank.arity(t)
        val k: Int = pos(depth)
        val args: IndexedSeq[K.Expression] =
          (0 until n).map(i => if i == k then kernelizeHole(bank.arg(t, i), vars, pos, depth + 1, hole) else kernelize(bank.arg(t, i), vars))
        applySymbol(bank.headSymbol(t), args)

    /** A kernel equality atom `a = b`, built with the exact constant [[kernelize]] produces for `=`. */
    private def mkEqK(a: K.Expression, b: K.Expression): K.Expression = applySymbol(EqualitySymbol, IndexedSeq(a, b))

    private var holeCounter: Int = 0

    /** A fresh `Ind` context variable for a substitution lambda, distinct from every `canonVar` (`reconV…`). */
    private def freshHole(): K.Variable =
      val h = K.Variable(K.Identifier("reconHole", holeCounter), K.Ind)
      holeCounter += 1
      h

    /**
     * Flip an equality on the **right** of a derived sequent: given a step `ref` proving `Γ ⊢ Δ, a=b`, emit a
     * short derivation of `Γ ⊢ Δ, b=a` (reflexivity + one `RightSubstEq` + a `Cut`) and return its reference and
     * sequent. Used to reorient a rewriting equation whose stored side order is the reverse of the one the
     * `SubstEq` step needs.
     */
    private def flipEqRight(ref: Int, seq: K.Sequent, a: K.Expression, b: K.Expression): (Int, K.Sequent) =
      val ab = mkEqK(a, b)
      val ba = mkEqK(b, a)
      val aa = mkEqK(a, a)
      val r1 = addStep(K.RightRefl(K.Sequent(Set.empty, Set(aa)), aa)) // ⊢ a=a
      val hole = freshHole()
      val r2 = addStep(K.RightSubstEq(K.Sequent(Set(ab), Set(ba)), r1, Seq((a, b)), (Seq(hole), mkEqK(hole, a)))) // a=b ⊢ b=a
      val outSeq = K.Sequent(seq.left, (seq.right - ab) + ba)
      (addStep(K.Cut(outSeq, ref, r2, ab)), outSeq)

    /** Parse an interned symbol name (a kernel `Identifier.toString`) back to the exact identifier,
     *  recovering a trailing counter index (`"e_1"` → `Identifier("e", 1)`). Inverse of the [[Bridge]]
     *  intern key, using the kernel's own `String`→`Identifier` conversion. Well-defined because every legal
     *  Lisa identifier is either `_`-free or a valid `name_counter` (the TPTP parser's `sanitize` guarantees
     *  this by escaping `_` to `$u`), so the `toString`/parse round-trip is lossless. */
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
