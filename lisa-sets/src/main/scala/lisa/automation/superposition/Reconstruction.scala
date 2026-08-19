package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.{Int2ObjectOpenHashMap, IntOpenHashSet}

import scala.collection.mutable

import lisa.utils.K
import lisa.automation.clausification.Clausification.GeneratedNames

import Core.*

/** Reconstruction of a refutation (the empty clause and its [[Justification]] DAG) into a Lisa kernel
  * [[lisa.utils.K.SCProof]] whose imports are the input clause-sequents and whose conclusion is the
  * empty sequent `⊢`.
  *
  * Each clause becomes one import or step. The README lists which kernel rules each inference maps to.
  *
  * The substitution is not stored during the search. it is recovered by re-unifying the recorded literals. */
object Reconstruction:

  /** An input clause's original sequent plus the map (internal var number → its original kernel variable). */
  type InputInfo = (K.Sequent, Map[Int, K.Variable])

  /** Reconstruct the refutation rooted at `empty` into a kernel proof. `inputs` maps each input clause's
    * id to its original sequent and variable map (supplied by [[Bridge]]). */
  def reconstruct(
      empty: Clause,
      bank: TermBank,
      inputs: collection.Map[Int, InputInfo],
      schematicIds: Set[K.Identifier] = Set.empty,
      discharge: Map[K.Variable, K.Expression] = Map.empty
  ): K.SCProof =
    new Builder(bank, inputs, schematicIds, discharge).reconstructProof(empty)

  private final class Builder(bank: TermBank, inputs: collection.Map[Int, InputInfo], schematicIds: Set[K.Identifier], discharge: Map[K.Variable, K.Expression]):
    private val sig: Signature = bank.signature
    private val steps: mutable.ArrayBuffer[K.SCProofStep] = mutable.ArrayBuffer.empty
    private val imports: mutable.ArrayBuffer[K.Sequent] = mutable.ArrayBuffer.empty
    private val memo: mutable.Map[Int, Recon] = mutable.Map.empty
    private val trail: Trail = new Trail(bank)
    // Abstraction discharge ([[Clausal]]), keyed by symbol name for [[kernelize]]: each schematic `F` maps to its
    // closed value `λfv. e`, inlined so the rebuilt proof carries `e` and never `F`. Empty for clausal input.
    private val dischargeById: Map[K.Identifier, K.Expression] = discharge.map((v, e) => v.id -> e)

    def reconstructProof(empty: Clause): K.SCProof =
      refOf(empty)
      K.SCProof(steps.toIndexedSeq, imports.toIndexedSeq)

    /** A reconstructed clause: its proof reference and kernel sequent (already in the canonical `cv…` naming). */
    private final case class Recon(ref: Int, seq: K.Sequent)

    private def addStep(s: K.SCProofStep): Int = { steps += s; steps.length - 1 }
    private def addImport(s: K.Sequent): Int = { imports += s; -imports.length }

    /** The canonical kernel variable `cvN` for internal variable `n`. The naming is global, shared across all
     *  clauses, which are instantiated independently, so it standardises the clauses apart. Every clause's
     *  sequent, and every `kernelize`d term, uses it, so it needs no per-clause threading. */
    private def canonVar(n: Int): K.Variable = K.Variable(K.Identifier(GeneratedNames.reconClauseVar, n), K.Ind)

    private def refOf(c: Clause): Recon = memo.getOrElseUpdate(c.id, build(c))

    private def build(c: Clause): Recon = c.justification match
      case Justification.Input => buildInput(c)
      case Justification.Canonicalization(p) => refOf(p) // sort/dedup are no-ops on a set-sequent
      case Justification.Factoring(p, i, j) => buildFactoring(p, i, j)
      case Justification.Resolution(l, i, r, j) => buildResolution(l, i, r, j)
      case Justification.Superposition(from, fi, fs, into, ii, pos) => buildSuperposition(from, fi, fs, into, ii, pos)
      case Justification.Demodulation(target, ti, pos, rule, rs) => buildDemodulation(target, ti, pos, rule, rs)
      case Justification.EqualityResolution(p, i) => buildEqualityResolution(p, i)
      case Justification.EqualityFactoring(p, d, ds, k, ks) => buildEqualityFactoring(p, d, ds, k, ks)

    /** Inline the abstraction discharge into a sequent: substitute every schematic `F` by its `λfv. e` value and
     *  β-normalise. Identity when nothing was abstracted. */
    private def dischargeSeq(s: K.Sequent): K.Sequent =
      if discharge.isEmpty then s
      else K.Sequent(s.left.map(e => K.substituteVariables(e, discharge).betaNormalForm), s.right.map(e => K.substituteVariables(e, discharge).betaNormalForm))

    private def buildInput(c: Clause): Recon =
      val (rawOrigSeq, vm) = inputs(c.id)
      val origSeq = dischargeSeq(rawOrigSeq) // present the import with `F` inlined back to its original subterm
      val imp = addImport(origSeq)
      if vm.isEmpty then Recon(imp, origSeq)
      else
        val subst: Map[K.Variable, K.Expression] = vm.map((n, ov) => ov -> (canonVar(n): K.Expression))
        val canonSeq = substSeq(origSeq, subst)
        Recon(addStep(K.InstSchema(canonSeq, imp, subst)), canonSeq)

    private def buildFactoring(parent: Clause, i: Int, j: Int): Recon =
      val p = refOf(parent)
      val saved = trail.save()
      trail.unify(bank.atomOf(parent.literals(i)), 0, bank.atomOf(parent.literals(j)), 0)
      val applier = trail.applier()
      replaySurvivors(applier, parent, skip = j, scope = 0) // fix the conclusion's variable numbering
      val subst = substOf(parent, applier, scope = 0)
      val bot = substSeq(p.seq, subst)
      trail.restore(saved)
      val (ref, seq) = instStep(p, subst, bot)
      Recon(ref, seq)

    private def buildResolution(left: Clause, i: Int, right: Clause, j: Int): Recon =
      val pl = refOf(left); val pr = refOf(right)
      val saved = trail.save()
      trail.unify(bank.atomOf(left.literals(i)), 0, bank.atomOf(right.literals(j)), 1)
      val applier = trail.applier()
      replaySurvivors(applier, left, skip = i, scope = 0)
      replaySurvivors(applier, right, skip = j, scope = 1)
      val substL = substOf(left, applier, scope = 0)
      val substR = substOf(right, applier, scope = 1)
      val botL = substSeq(pl.seq, substL)
      val botR = substSeq(pr.seq, substR)
      val phi = K.substituteVariables(kernelize(bank.atomOf(left.literals(i))), substL)
      trail.restore(saved)
      val (refL, seqL) = instStep(pl, substL, botL)
      val (refR, seqR) = instStep(pr, substR, botR)
      // the positive side carries φ on the right (Cut's t1); the negative side carries it on the left (t2)
      val (t1ref, t1seq, t2ref, t2seq) =
        if bank.isPositive(left.literals(i)) then (refL, seqL, refR, seqR) else (refR, seqR, refL, seqL)
      val resolvent = K.Sequent(t1seq.left ++ (t2seq.left - phi), (t1seq.right - phi) ++ t2seq.right)
      Recon(addStep(K.Cut(resolvent, t1ref, t2ref, phi)), resolvent)

    // --- equality inferences ------------------------------------------------------------------------------
    //
    // Superposition and demodulation share one shape ([[buildRewrite]]): instantiate both parents by the
    // recomputed unifier/matcher, `SubstEq` the rewritten literal in the *into/target* instance, adding `l=r` to
    // its antecedent, then `Cut` the *from/rule* instance against it. Equality resolution collapses a unified
    // disequality with `LeftRefl`; equality factoring is one `RightSubstEq`, plus a reorientation if the sides
    // disagree.

    private def buildSuperposition(from: Clause, iFrom: Int, fromSide: Int, into: Clause, iInto: Int, pos: Array[Int]): Recon =
      val fromAtom = bank.atomOf(from.literals(iFrom))
      val l = bank.arg(fromAtom, fromSide)
      buildRewrite(
        from, iFrom, fromSide, into, iInto, pos,
        establish = () => { trail.unify(l, 0, Superposition.subtermAt(bank, bank.atomOf(into.literals(iInto)), pos), 1); () },
        replay = ap => Superposition.replayApplier(bank, ap, from, iFrom, fromSide, into, iInto)
      )

    private def buildDemodulation(target: Clause, iTarget: Int, pos: Array[Int], rule: Clause, ruleSide: Int): Recon =
      val ruleAtom = bank.atomOf(rule.literals(0)) // the demodulator is a positive unit equality
      val l = bank.arg(ruleAtom, ruleSide)
      buildRewrite(
        rule, 0, ruleSide, target, iTarget, pos,
        establish = () => { trail.matchTerm(l, 0, Superposition.subtermAt(bank, bank.atomOf(target.literals(iTarget)), pos), 1); () },
        replay = ap => Demodulation.replayApplier(bank, ap, rule, ruleSide, target)
      )

    /** The common superposition/demodulation reconstruction: `from` (scope 0) rewrites `into`'s literal `iInto`
      * at subterm `pos` with the equation on `from`'s side `fromSide`. `establish` re-binds the trail with the
      * unifier (superposition) or matcher (demodulation); `replay` re-runs the [[Trail.Applier]] in the
      * generating code's order so the conclusion's fresh variables match `c`. Emits a `SubstEq` (Right if the
      * rewritten literal is positive, else Left) that adds `lσ=rσ` to the antecedent, then a `Cut` on `lσ=rσ`. */
    private def buildRewrite(
        from: Clause, iFrom: Int, fromSide: Int, into: Clause, iInto: Int, pos: Array[Int],
        establish: () => Unit, replay: trail.Applier => Unit): Recon =
      val pFrom = refOf(from); val pInto = refOf(into)
      val fromAtom = bank.atomOf(from.literals(iFrom))
      val intoLit = into.literals(iInto)
      val intoAtom = bank.atomOf(intoLit)
      val saved = trail.save()
      establish()
      val applier = trail.applier()
      replay(applier)
      val substFrom = substOf(from, applier, scope = 0)
      val substInto = substOf(into, applier, scope = 1)
      val botFrom = substSeq(pFrom.seq, substFrom)
      val botInto = substSeq(pInto.seq, substInto)
      // the equation's two stored sides (a0=a1 on `from`'s right) and the rewrite's occurrence sK → replacement tK
      val a0 = K.substituteVariables(kernelize(bank.arg(fromAtom, 0)), substFrom)
      val a1 = K.substituteVariables(kernelize(bank.arg(fromAtom, 1)), substFrom)
      val sK = K.substituteVariables(kernelize(Superposition.subtermAt(bank, intoAtom, pos)), substInto)
      val tK = if fromSide == 0 then a1 else a0 // the replacement is the equation's *other* stored side
      val hole = freshHole()
      val phiBody = K.substituteVariables(kernelizeHole(intoAtom, pos, 0, hole), substInto)
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
      Recon(addStep(K.Cut(concl, refFrom, refSubst, eq)), concl)

    private def buildEqualityResolution(parent: Clause, i: Int): Recon =
      val pC = refOf(parent)
      val atom = bank.atomOf(parent.literals(i)) // the negative equality s ≉ t
      val saved = trail.save()
      trail.unify(bank.arg(atom, 0), 0, bank.arg(atom, 1), 0)
      val applier = trail.applier()
      replaySurvivors(applier, parent, skip = i, scope = 0)
      val substC = substOf(parent, applier, scope = 0)
      val botC = substSeq(pC.seq, substC)
      val refl = K.substituteVariables(kernelize(atom), substC) // sσ = sσ, reflexive after unification
      trail.restore(saved)
      val (refC, seqC) = instStep(pC, substC, botC)
      val concl = K.Sequent(seqC.left - refl, seqC.right)
      Recon(addStep(K.LeftRefl(concl, refC, refl)), concl)

    private def buildEqualityFactoring(parent: Clause, i: Int, iSide: Int, j: Int, jSide: Int): Recon =
      val pC = refOf(parent)
      val atomI = bank.atomOf(parent.literals(i)) // dropped equality s ≈ t (factored side iSide = s)
      val s = bank.arg(atomI, iSide); val t = bank.arg(atomI, 1 - iSide)
      val atomJ = bank.atomOf(parent.literals(j)) // the kept partner equality s' ≈ t'
      val tp = bank.arg(atomJ, 1 - jSide) // partner's other side t'
      val saved = trail.save()
      trail.unify(s, 0, bank.arg(atomJ, jSide), 0) // σ = mgu(s, s')
      val applier = trail.applier()
      Superposition.replayFactoringApplier(bank, applier, parent, i, iSide, j, jSide)
      val substC = substOf(parent, applier, scope = 0)
      val botC = substSeq(pC.seq, substC)
      val hole = freshHole()
      val phiBody = K.substituteVariables(kernelizeHole(atomI, Array(1 - iSide), 0, hole), substC)
      val tK = K.substituteVariables(kernelize(t), substC) // tσ
      val tpK = K.substituteVariables(kernelize(tp), substC) // t'σ
      val pK = K.substituteVariables(kernelize(s), substC) // sσ = s'σ (the shared maximal side)
      val phiOfS = K.substituteVariables(phiBody, Map(hole -> tK)) // literal i's atom instance (φ(s))
      val phiOfT = K.substituteVariables(phiBody, Map(hole -> tpK)) // the rewritten atom (φ(t)) in atom i's side order
      val eq = mkEqK(tK, tpK) // the introduced disequality's atom tσ = t'σ (added to the antecedent)
      trail.restore(saved)
      val (refC, seqC) = instStep(pC, substC, botC)
      // rewrite literal i (P≈tσ, on the right) to P≈t'σ using tσ=t'σ; adds tσ≠t'σ to the left (the new negative literal)
      val bot1 = K.Sequent(seqC.left + eq, (seqC.right - phiOfS) + phiOfT)
      val step1 = addStep(K.RightSubstEq(bot1, refC, Seq((tK, tpK)), (Seq(hole), phiBody)))
      // φ(t) came out in literal i's side order; if the kept partner j stores the reverse order, reorient it to merge
      if iSide == jSide then Recon(step1, bot1)
      else
        val (fa, fb) = if iSide == 0 then (pK, tpK) else (tpK, pK) // the two sides of φ(t), stored order
        val (step2, bot2) = flipEqRight(step1, bot1, fa, fb)
        Recon(step2, bot2)

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

    /** The kernel substitution instantiating `parent`'s variables under the trail, both the domain and the
     *  images named by the canonical [[canonVar]] scheme. */
    private def substOf(parent: Clause, applier: trail.Applier, scope: Scope): Map[K.Variable, K.Expression] =
      bank.varsOf(parent).iterator.map(v => canonVar(bank.varNum(v).num) -> kernelize(applier.apply(v, scope))).toMap

    private def substSeq(s: K.Sequent, subst: Map[K.Variable, K.Expression]): K.Sequent =
      if subst.isEmpty then s
      else K.Sequent(s.left.map(K.substituteVariables(_, subst)), s.right.map(K.substituteVariables(_, subst)))

    /** Convert an internal term to a kernel expression, mapping internal variable numbers via [[canonVar]]. */
    private def kernelize(t: Term): K.Expression =
      val cached: K.Expression = kernelCache.get(t.offset)
      if cached != null then cached
      else
        val e: K.Expression =
          if bank.isVar(t) then canonVar(bank.varNum(t).num)
          else
            val n = bank.arity(t)
            val args: IndexedSeq[K.Expression] = (0 until n).map(k => kernelize(bank.arg(t, k)))
            applySymbol(bank.headSymbol(t), args)
        kernelCache.put(t.offset, e)
        e

    // Kernelised terms, keyed by arena offset. `kernelize` is a pure function of the term -- variables go
    // through `canonVar`, symbols through `headExpr`, and the discharge is fixed for this Builder -- and terms
    // are hash-consed, so one offset is one structure. Identical subterms therefore convert once for the whole
    // proof: within a step, where the rewritten atom is walked both whole and with a hole, and across steps,
    // where a clause reappears as a parent.
    private val kernelCache: Int2ObjectOpenHashMap[K.Expression] = new Int2ObjectOpenHashMap()

    /** Apply interned symbol `head` to already-kernelised `args`, honouring the abstraction discharge (inline a
     *  higher-order term). */
    private def applySymbol(head: Symbol, args: IndexedSeq[K.Expression]): K.Expression =
      args.foldLeft(headExpr(head))((acc, a) => K.Application(acc, a)) match
        case applied if dischargedIds.contains(head.code) => applied.betaNormalForm // an inlined `λfv. e`
        case applied => applied

    /** The kernel head a symbol becomes, before its arguments: its discharge value, or the constant/variable
     *  built from its identifier. Cached, since it depends on the symbol alone. */
    private def headExpr(head: Symbol): K.Expression =
      val cached: K.Expression = headCache(head.code)
      if cached != null then cached
      else
        val info: SymbolInfo = sig.info(head)
        // The signature carries the identifier's two parts, so it is rebuilt rather than parsed back out of a
        // `name_no` string: `Identifier("e", 1)`, never the wrong `Identifier("e_1", 0)`.
        val id: K.Identifier = K.Identifier(info.name, info.no)
        val hd: K.Expression = dischargeById.get(id) match
          case Some(lam) => dischargedIds.add(head.code); lam
          case None =>
            val sort: K.Sort = sortFor(info.arity, info.isPredicate)
            if schematicIds.contains(id) then K.Variable(id, sort) else K.Constant(id, sort)
        headCache(head.code) = hd
        hd

    // Per-symbol kernel heads, indexed by symbol code; `null` until first use. `dischargedIds` marks the ones
    // whose head is a `λfv. e` value, so the application above knows to β-normalise.
    private val headCache: Array[K.Expression] = new Array[K.Expression](sig.size)
    private val dischargedIds: IntOpenHashSet = new IntOpenHashSet()

    /** Kernelise `t` but emit `hole` in place of the subterm at position `pos` (a path of argument indices),
     *  yielding a context `φ(hole)`; everything off the path is kernelised normally via [[kernelize]]. */
    private def kernelizeHole(t: Term, pos: Array[Int], depth: Int, hole: K.Variable): K.Expression =
      if depth == pos.length then hole
      else
        val n: Int = bank.arity(t)
        val k: Int = pos(depth)
        val args: IndexedSeq[K.Expression] =
          (0 until n).map(i => if i == k then kernelizeHole(bank.arg(t, i), pos, depth + 1, hole) else kernelize(bank.arg(t, i)))
        applySymbol(bank.headSymbol(t), args)

    /** A kernel equality atom `a = b`, built with the exact constant [[kernelize]] produces for `=`. */
    private def mkEqK(a: K.Expression, b: K.Expression): K.Expression = applySymbol(EqualitySymbol, IndexedSeq(a, b))

    private var holeCounter: Int = 0

    /** A fresh `Ind` context variable for a substitution lambda, distinct from every `canonVar` (`cv…`). */
    private def freshHole(): K.Variable =
      val h = K.Variable(K.Identifier(GeneratedNames.hole, holeCounter), K.Ind)
      holeCounter += 1
      h

    /** Flip an equality on the **right** of a derived sequent: given a step `ref` proving `Γ ⊢ Δ, a=b`, emit a
      * short derivation of `Γ ⊢ Δ, b=a` (reflexivity + one `RightSubstEq` + a `Cut`) and return its reference and
      * sequent. Used to reorient a rewriting equation whose stored side order is the reverse of the one the
      * `SubstEq` step needs. */
    private def flipEqRight(ref: Int, seq: K.Sequent, a: K.Expression, b: K.Expression): (Int, K.Sequent) =
      val ab = mkEqK(a, b)
      val ba = mkEqK(b, a)
      val aa = mkEqK(a, a)
      val r1 = addStep(K.RightRefl(K.Sequent(Set.empty, Set(aa)), aa)) // ⊢ a=a
      val hole = freshHole()
      val r2 = addStep(K.RightSubstEq(K.Sequent(Set(ab), Set(ba)), r1, Seq((a, b)), (Seq(hole), mkEqK(hole, a)))) // a=b ⊢ b=a
      val outSeq = K.Sequent(seq.left, (seq.right - ab) + ba)
      (addStep(K.Cut(outSeq, ref, r2, ab)), outSeq)


    /** The kernel sort of a symbol: `Ind → … → Ind → (Prop|Ind)` with `arity` argument places. */
    private def sortFor(arity: Int, isPredicate: Boolean): K.Sort =
      var s: K.Sort = if isPredicate then K.Prop else K.Ind
      var k = 0
      while k < arity do { s = K.Ind -> s; k += 1 }
      s

