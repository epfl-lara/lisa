package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.IntOpenHashSet

import scala.collection.mutable

import Core.*

/**
 * The DISCOUNT (given-clause) saturation loop for Phase-1 ordered resolution + factoring.
 *
 * Two clause stores: a `passive` (unprocessed) set, kept in two lazy-deletion priority queues so the
 * next given clause can be picked by an age/weight ratio; and an `active` (processed) set scanned
 * linearly for inferences (term indexing is Phase 4). Each iteration selects a given clause, computes
 * its selected literals, moves it into active, generates all resolvents against the active set and all
 * factors of itself, and inserts the (canonicalised, non-tautological) survivors back into passive. It
 * stops at the empty clause `□` (refutation) or when the passive set empties (saturation); `maxGiven`
 * bounds the work otherwise.
 *
 * Phase-2 simplification adds θ-**subsumption** (via [[Subsumption.subsumes]]) and **unit deletion** (the
 * unit case of subsumption resolution, via [[Subsumption.unitDeletionResolvent]]), both against the active
 * set only (passive-redundant clauses are caught lazily when selected). One combined scan per direction:
 * *forward* (in [[forwardSimplify]]) discards or shrinks a new/just-selected clause; *backward* (in
 * [[backwardSimplify]]) deletes or shrinks active clauses, run before the given joins active. Subsumption
 * deletion needs no reconstruction (a deleted clause never enters `□`'s [[Justification]] DAG), and a
 * unit-deletion result is an ordinary resolvent (`Inference.resolve`), so it reconstructs with no new
 * machinery either. Demodulation and term indexing are still Phases 3 and 4. On a refutation the loop
 * returns the empty clause, whose DAG later feeds reconstruction.
 */
object Discount:
  enum Result:
    case Refutation(empty: Clause)
    case Saturated
    case Unknown

final class Discount(
    bank: TermBank,
    trail: Trail,
    ageRatio: Int = 1,
    weightRatio: Int = 1,
    factorAfterCheck: Boolean = false,
    forwardSubsumption: Boolean = true,
    backwardSubsumption: Boolean = true,
    forwardUnitDeletion: Boolean = true,
    backwardUnitDeletion: Boolean = true,
    // General (multi-literal side) subsumption resolution. Off by default: unlike unit deletion (which only
    // fires for unit side clauses), it runs a match search for *every* non-subsuming active clause, so
    // without term indexing (Phase 4) it is a much heavier forward/backward cost of uncertain payoff.
    forwardSubsumptionResolution: Boolean = false,
    backwardSubsumptionResolution: Boolean = false,
    // Condensation: replace a new clause by an equivalent shorter factor of itself. Clause-local (no active
    // scan), applied once at creation. Off by default pending its seed-42 ablation.
    condensation: Boolean = false,
    // Off by default: with no term indexing (Phase 4), forward-simplifying every *generated* clause costs
    // an O(|active|) scan per clause and is empirically a net loss -- the mandatory selection-time pass
    // still catches every redundant clause before it activates. Revisit once indexing makes it cheap.
    // (seed-42 ablation: gen=67 refuted vs nogen=71, strictly more, no regressions. See Benchmarks.md.)
    // Governs forward subsumption *and* forward unit deletion at the generation point.
    forwardSimplifyAtGeneration: Boolean = false,
    // Master equality switch. When off, **every** equality-specific part of the loop is skipped --
    // superposition, equality resolution, equality factoring, and forward/backward demodulation (plus the
    // demodulator upkeep) -- reducing the loop to pure ordered resolution + factoring. Set it off for
    // equality-free problems (nothing is lost, and the equality enumerations/upkeep are not paid for); the
    // finer-grained flags below then have no effect. On (the default), each equality inference is governed by
    // its own flag.
    equality: Boolean = true,
    // Generating equality inferences. Equality resolution/factoring are always run when `equality` is on
    // (inert without equality literals); this flag gates the heavier superposition enumeration (both
    // directions) at activation.
    superposition: Boolean = true,
    // Demodulation (rewriting by active positive unit equalities): forward normal-forms the given at
    // selection; backward rewrites active clauses when the given is a new unit equality. Inert without them.
    forwardDemodulation: Boolean = true,
    backwardDemodulation: Boolean = true):
  import Discount.Result

  // Effective equality-inference switches: each is the master `equality` flag AND its own flag. When
  // `equality` is off they are all false, so every equality-specific inference and its upkeep is skipped.
  private val superpositionOn: Boolean = equality && superposition
  private val forwardDemodulationOn: Boolean = equality && forwardDemodulation
  private val backwardDemodulationOn: Boolean = equality && backwardDemodulation

  // Simplification counters (observability / benchmarks); reset at the start of each `saturate`.
  var forwardSubsumed: Int = 0
  var backwardSubsumed: Int = 0
  var forwardUnitDeleted: Int = 0
  var backwardUnitDeleted: Int = 0
  var forwardSubsumptionResolved: Int = 0 // multi-literal-side forward SR
  var backwardSubsumptionResolved: Int = 0
  var condensed: Int = 0

  // Passive set: two views over the same clauses, with lazy deletion -- a clause selected via one
  // stays a stale entry in the other, skipped on pop. Age is just a FIFO queue: clauses are enqueued
  // in strictly increasing `id` order (ids are monotonic and each insertion is a fresh clause), so
  // dequeuing from the front already yields the oldest. Weight needs a real min-heap on (weight, id).
  private val byAge: mutable.Queue[Clause] = mutable.Queue.empty
  // Reversed for a min-heap (PriorityQueue is a max-heap): the lighter clause -- ties broken by the
  // smaller id, i.e. the older -- has the highest priority. A direct Int comparison, so no Tuple2 is
  // allocated (and no Int boxing) per heap comparison.
  private val byWeightOrder: Ordering[Clause] = (a, b) =>
    val w = Integer.compare(b.weight, a.weight)
    if w != 0 then w else Integer.compare(b.id, a.id)
  private val byWeight: mutable.PriorityQueue[Clause] = new mutable.PriorityQueue[Clause]()(using byWeightOrder)
  private val livePassive: IntOpenHashSet = new IntOpenHashSet() // ids still in passive
  private var balance: Int = 0 // age/weight alternation, Vampire-style

  // Active (processed) set, scanned linearly (indexing is Phase 4).
  private val active: mutable.ArrayBuffer[Clause] = mutable.ArrayBuffer.empty

  // The active demodulators: rewrite rules from the positive unit equalities in `active`, maintained
  // incrementally (added on activation, dropped on deletion) so forward demodulation needn't re-filter
  // `active` and re-extract `rules` on every given.
  private val activeDemodulators: mutable.ArrayBuffer[Demodulation.Rule] = mutable.ArrayBuffer.empty

  // Ordering used only for the (optional) post-unification σ-maximality check on factors.
  private def kbo: KBO = bank.order.kbo // the bank's shared KBO (post-unification σ-maximality check on factors)

  /**
   * Saturate `initial` (plus everything derived from it). Returns [[Result.Refutation]] with the empty
   * clause if `□` is derived, [[Result.Saturated]] if the passive set empties without one, or
   * [[Result.Unknown]] if the `maxGiven` given-clause budget or the `maxMillis` wall-clock budget is
   * reached first. The time budget is checked once per given clause (cheap), so the loop stops cleanly
   * rather than relying on the caller to abandon a runaway thread.
   */
  def saturate(initial: Seq[Clause], maxGiven: Int = Int.MaxValue, maxMillis: Long = Long.MaxValue): Result =
    byAge.clear(); byWeight.clear(); livePassive.clear(); active.clear(); activeDemodulators.clear(); balance = 0
    forwardSubsumed = 0; backwardSubsumed = 0; forwardUnitDeleted = 0; backwardUnitDeleted = 0
    forwardSubsumptionResolved = 0; backwardSubsumptionResolved = 0; condensed = 0
    val it = initial.iterator
    while it.hasNext do
      addPassive(it.next()) match
        case Some(empty) => return Result.Refutation(empty)
        case None => ()
    val checkTime: Boolean = maxMillis != Long.MaxValue
    val deadline: Long = if checkTime then System.nanoTime() + maxMillis * 1000000L else 0L
    var givenCount = 0
    while !livePassive.isEmpty && givenCount < maxGiven && (!checkTime || System.nanoTime() < deadline) do
      val gc = forwardDemodulate(popGiven()) // normal-form the given against active demodulators, then simplify
      // forward simplify the given against active: it may have been subsumed (skip) or shrunk by unit
      // deletion (process the shorter clause) by clauses that became active while it sat in passive.
      // A skip is not counted as a processed given (count activations only).
      (if forwardSubsumption || forwardUnitDeletion then forwardSimplify(gc) else Some(gc)) match
        case None => () // subsumed at selection: drop it
        case Some(g) =>
          if g.isEmpty then return Result.Refutation(g) // unit deletion closed the clause
          else
            givenCount += 1
            activate(g) match
              case Some(empty) => return Result.Refutation(empty)
              case None => ()
    if livePassive.isEmpty then Result.Saturated else Result.Unknown

  /** Canonicalise `c` and add it to passive; returns the empty clause if `c` is (or simplifies to) `□`.
   *  Immediate (clause-local) simplification -- canonicalisation then condensation -- is applied first; then,
   *  when [[forwardSimplifyAtGeneration]] is on, `c` is forward-simplified against active (subsumed ⇒
   *  discarded, shrunk ⇒ the shorter clause enqueued). Forward simplification at generation is off by
   *  default -- the given is forward-simplified at selection regardless. */
  private def addPassive(c: Clause): Option[Clause] =
    Inference.canonicalize(bank, c) match
      case None => None // tautology: discard
      case Some(cc0) =>
        if cc0.isEmpty then Some(cc0)
        else
          // condensation: clause-local, run on every new clause (cannot produce □ or a tautology)
          val cc: Clause =
            if condensation then
              val cd: Clause = Subsumption.condense(bank, trail, cc0)
              if cd ne cc0 then condensed += 1
              cd
            else cc0
          val simplified: Option[Clause] =
            if forwardSimplifyAtGeneration && (forwardSubsumption || forwardUnitDeletion) then forwardSimplify(cc)
            else Some(cc)
          simplified match
            case None => None // subsumed by an active clause: discard
            case Some(cc) =>
              if cc.isEmpty then Some(cc) // unit deletion closed it
              else
                byAge.enqueue(cc)
                byWeight.enqueue(cc)
                livePassive.add(cc.id)
                None

  /** Pick the next given clause by the age/weight ratio, removing it from passive: scan the chosen
   *  queue, skipping stale (already-selected) entries. A live clause is guaranteed when the passive set
   *  is non-empty (the caller checks `livePassive`), since every passive clause sits in both queues.
   *  The scan is inlined per queue rather than factored into a by-name helper, so no thunk is allocated
   *  per call. */
  private def popGiven(): Clause =
    if balance > 0 || (balance == 0 && ageRatio <= weightRatio) then
      balance -= ageRatio
      while byWeight.nonEmpty do
        val c: Clause = byWeight.dequeue()
        if takeLive(c) then return c
    else
      balance += weightRatio
      while byAge.nonEmpty do
        val c: Clause = byAge.dequeue()
        if takeLive(c) then return c
    throw new IllegalStateException("popGiven called on an empty passive set")

  /** If `c` is still live (in passive), mark it not-live and return `true`; if stale, return `false`. */
  private def takeLive(c: Clause): Boolean =
    if livePassive.contains(c.id) then { livePassive.remove(c.id); true }
    else false

  /** Move `gc` into active and generate all resolvents (against active) and factors (of itself).
   *  Backward simplification first deletes/shrinks active clauses using `gc` -- run before `gc` joins
   *  active (so it never simplifies itself) and before generation (so deleted clauses produce no
   *  inferences). A backward unit deletion that closes a clause to `□` is returned as a refutation. */
  private def activate(gc: Clause): Option[Clause] =
    val gSel: Array[Int] = gc.select(bank)
    if backwardSubsumption || backwardUnitDeletion then
      backwardSimplify(gc) match
        case Some(empty) => return Some(empty)
        case None => ()
    backwardDemodulateStep(gc) match // if `gc` is a new unit equality, rewrite active clauses (before it joins active)
      case Some(empty) => return Some(empty)
      case None => ()
    active += gc
    if forwardDemodulationOn && isPosUnitEq(gc) then activeDemodulators ++= Demodulation.rules(bank, bank.order, gc) // gc is a new demodulator
    // Precompute once per activation (invariant across the active scan): which of gc's selected literals are
    // non-equality (for ordinary resolution) and gc's usable superposition from-sides.
    val gcSelNonEq: Array[Boolean] = new Array[Boolean](gSel.length)
    var gm = 0
    while gm < gSel.length do { gcSelNonEq(gm) = !isEquality(gc.literals(gSel(gm))); gm += 1 }
    val gcFromSides: List[(Int, Int, Term, Symbol)] = if superpositionOn then fromSides(gc, gSel) else Nil
    // resolution + superposition against each active clause (gc now included, so self-inferences fire)
    var ai = 0
    while ai < active.length do
      val a: Clause = active(ai)
      val aSel: Array[Int] = a.select(bank)
      var gi = 0
      while gi < gSel.length do
        if gcSelNonEq(gi) then // equalities go to superposition / equality resolution, not here
          var aj = 0
          while aj < aSel.length do
            if !isEquality(a.literals(aSel(aj))) then
              Inference.resolve(bank, trail, gc, gSel(gi), a, aSel(aj)) match
                case Some(r) =>
                  addPassive(r) match
                    case Some(empty) => return Some(empty)
                    case None => ()
                case None => ()
            aj += 1
        gi += 1
      // superposition: gc's equations into `a` (precomputed from-sides), and `a`'s equations into gc (both
      // directions; the a == gc self-pair is done once). The caller locates + unifies; `superpose` is build-only.
      if superpositionOn then
        superposeUsing(gc, gcFromSides, a, aSel) match
          case Some(empty) => return Some(empty)
          case None => ()
        if a.id != gc.id then
          superposeFromInto(a, aSel, gc, gSel) match
            case Some(empty) => return Some(empty)
            case None => ()
      ai += 1
    // factoring: each unordered pair of distinct selected, positive, non-equality literals, once
    // (positive factoring only; equalities get equality-factoring in Phase 3). A literal that unifies
    // with a selected (maximal) one is itself maximal, hence also selected, so pairing within the
    // selected set loses nothing. If `factorAfterCheck`, drop a factor whose kept literal is no longer
    // (KBO-)maximal under the unifier.
    var gi2 = 0
    while gi2 < gSel.length do
      val i: Int = gSel(gi2)
      if bank.isPositive(gc.literals(i)) && !isEquality(gc.literals(i)) then
        var gj = gi2 + 1
        while gj < gSel.length do
          val j: Int = gSel(gj)
          if !isEquality(gc.literals(j)) then
            Inference.factor(bank, trail, gc, i, j) match
              case Some(f) =>
                if !factorAfterCheck || keptMaximal(f, if i < j then i else i - 1) then
                  addPassive(f) match
                    case Some(empty) => return Some(empty)
                    case None => ()
              case None => ()
          gj += 1
      gi2 += 1
    // equality resolution + equality factoring on the given (unary; enumerate all over the eligible set)
    if equality then
      val order: Order = bank.order
      addAll(Superposition.equalityResolution(bank, trail, order, gc, gSel)) match
        case Some(empty) => return Some(empty)
        case None => ()
      addAll(Superposition.equalityFactoring(bank, trail, order, gc, gSel)) match
        case Some(empty) => return Some(empty)
        case None => ()
    None

  /** Add each of `cs` to passive; returns `Some(□)` as soon as one is (or simplifies to) the empty clause. */
  private def addAll(cs: List[Clause]): Option[Clause] =
    var xs = cs
    while xs.nonEmpty do
      addPassive(xs.head) match
        case Some(empty) => return Some(empty)
        case None => ()
      xs = xs.tail
    None

  /** `c`'s usable superposition from-sides: `(iFrom, fromSide, l, lHead)` for each eligible positive-equality
   *  literal and each usable side (the `Gt` side, both if incomparable; never a variable side). Computed once
   *  per activation for the given, since they're invariant across the active scan. */
  private def fromSides(c: Clause, sel: Array[Int]): List[(Int, Int, Term, Symbol)] =
    val order: Order = bank.order
    val out = List.newBuilder[(Int, Int, Term, Symbol)]
    var i = 0
    while i < sel.length do
      val iFrom: Int = sel(i)
      val lit: Literal = c.literals(iFrom)
      val atom: Term = bank.atomOf(lit)
      if bank.isPositive(lit) && bank.headSymbol(atom) == EqualitySymbol then
        val ori: Cmp = order.orient(atom)
        var side = 0
        while side < 2 do
          val use: Boolean = ori match
            case Cmp.Gt => side == 0
            case Cmp.Lt => side == 1
            case Cmp.Inc => true
            case Cmp.Eq => false
          if use then
            val l: Term = bank.arg(atom, side)
            if !bank.isVar(l) then out += ((iFrom, side, l, bank.headSymbol(l)))
          side += 1
      i += 1
    out.result()

  /** Superpose with each of `fromC`'s precomputed `fromSides` into `intoC`'s eligible literals (`intoSel`). */
  private def superposeUsing(fromC: Clause, sides: List[(Int, Int, Term, Symbol)], intoC: Clause, intoSel: Array[Int]): Option[Clause] =
    var fs = sides
    while fs.nonEmpty do
      val (iFrom, fromSide, l, lHead) = fs.head
      var ii = 0
      while ii < intoSel.length do
        superposeAtPositions(fromC, iFrom, fromSide, l, lHead, intoC, intoSel(ii)) match
          case Some(empty) => return Some(empty)
          case None => ()
        ii += 1
      fs = fs.tail
    None

  /** All superpositions with `fromC` supplying the equation (eligible positive equalities in `fromSel`) into
   *  `intoC`'s eligible literals (`intoSel`): usable `fromSide`s (the `Gt` side, both if incomparable) × every
   *  non-variable into-subterm, head-pre-checked before unifying. Results go to `addPassive`; `Some(□)` on refutation. */
  private def superposeFromInto(fromC: Clause, fromSel: Array[Int], intoC: Clause, intoSel: Array[Int]): Option[Clause] =
    val order: Order = bank.order
    var fi = 0
    while fi < fromSel.length do
      val iFrom: Int = fromSel(fi)
      val fromLit: Literal = fromC.literals(iFrom)
      val fromAtom: Term = bank.atomOf(fromLit)
      if bank.isPositive(fromLit) && bank.headSymbol(fromAtom) == EqualitySymbol then
        val ori: Cmp = order.orient(fromAtom)
        var fromSide = 0
        while fromSide < 2 do
          val useSide: Boolean = ori match
            case Cmp.Gt => fromSide == 0
            case Cmp.Lt => fromSide == 1
            case Cmp.Inc => true
            case Cmp.Eq => false
          if useSide then
            val l: Term = bank.arg(fromAtom, fromSide)
            if !bank.isVar(l) then // no superposition from a variable side
              val lHead: Symbol = bank.headSymbol(l)
              var ii = 0
              while ii < intoSel.length do
                val iInto: Int = intoSel(ii)
                superposeAtPositions(fromC, iFrom, fromSide, l, lHead, intoC, iInto) match
                  case Some(empty) => return Some(empty)
                  case None => ()
                ii += 1
          fromSide += 1
      fi += 1
    None

  /** Walk the non-variable subterms of `intoC`'s literal `iInto`; where the head matches the from-side `l`,
   *  save + unify + build-only `superpose` + `addPassive`. Returns `Some(□)` on refutation. */
  private def superposeAtPositions(fromC: Clause, iFrom: Int, fromSide: Int, l: Term, lHead: Symbol,
                                   intoC: Clause, iInto: Int): Option[Clause] =
    val intoAtom: Term = bank.atomOf(intoC.literals(iInto))
    var refut: Option[Clause] = None
    Superposition.foreachSubterm(bank, intoAtom) { (u, path) =>
      if bank.headSymbol(u) == lHead then // cheap head pre-check (u and l both non-variable)
        val saved: Int = trail.save()
        if trail.unify(l, 0, u, 1) then
          Superposition.superpose(bank, trail, bank.order, fromC, iFrom, fromSide, intoC, iInto, path) match
            case Some(rr) =>
              addPassive(rr) match
                case Some(empty) => refut = Some(empty)
                case None => ()
            case None => ()
        trail.restore(saved)
      refut.isDefined // stop the walk if we've derived □
    }
    refut

  /** Forward simplify `m` against the active set in one scan (active only -- DISCOUNT does not
   *  forward-check passive): if some active clause subsumes `m`, return `None` (discard it); otherwise apply
   *  subsumption resolution by active clauses (unit deletion for unit sides, general SR for longer ones),
   *  returning the (possibly shrunk) clause -- `Some(□)` if a resolution closed it. A single pass: after a
   *  shrink the scan continues with the shorter clause, residual redundancy caught when it is later selected. */
  private def forwardSimplify(m0: Clause): Option[Clause] =
    var m: Clause = m0
    var i = 0
    while i < active.length do
      val c: Clause = active(i)
      if forwardSubsumption && Subsumption.subsumes(bank, trail, c, m) then
        forwardSubsumed += 1
        return None // subsumed: discard `m`
      // resolution arm runs only on clauses `c` does not subsume; gated by side size + flag
      if (if c.size == 1 then forwardUnitDeletion else forwardSubsumptionResolution) then
        Subsumption.subsumptionResolutionResolvent(bank, trail, c, m) match
          case Some(r) => // `r` is the canonical shrunk clause (it entails `m`)
            if c.size == 1 then forwardUnitDeleted += 1 else forwardSubsumptionResolved += 1
            if r.isEmpty then return Some(r) // resolution closed the clause
            m = r // continue the scan with the shrunk clause
          case None => ()
      i += 1
    Some(m)

  /** Backward simplify the active set using `gc` in one scan (`gc` not yet in active): delete each active
   *  clause `gc` subsumes, and shrink each that `gc` subsumption-resolves a literal from (unit deletion if
   *  `gc` is a unit, general SR otherwise). The shrunk clause is re-added through [[addPassive]] after the
   *  scan, to avoid mutating `active` mid-iteration. Removal is swap-with-last + truncate (O(1)); `active`
   *  is unordered, so reordering is harmless, and the swapped-in element is re-checked by *not* advancing the
   *  index. Returns `Some(□)` if a resolution closes a clause. Deletion needs no reconstruction; a shrunk
   *  clause is an ordinary resolvent. */
  private def backwardSimplify(gc: Clause): Option[Clause] =
    val gcUnit: Boolean = gc.size == 1
    val srOn: Boolean = if gcUnit then backwardUnitDeletion else backwardSubsumptionResolution
    var shrunk: mutable.ArrayBuffer[Clause] = null // re-added after the scan (lazily allocated)
    var i = 0
    while i < active.length do
      val m: Clause = active(i)
      var removed = false
      if backwardSubsumption && Subsumption.subsumes(bank, trail, gc, m) then
        backwardSubsumed += 1
        removed = true
      else if srOn then
        Subsumption.subsumptionResolutionResolvent(bank, trail, gc, m) match
          case Some(r) =>
            if gcUnit then backwardUnitDeleted += 1 else backwardSubsumptionResolved += 1
            if shrunk == null then shrunk = mutable.ArrayBuffer.empty
            shrunk += r
            removed = true
          case None => ()
      if removed then
        if isPosUnitEq(m) then removeDemodulatorsOf(m) // keep the demodulator set in sync
        active(i) = active(active.length - 1)
        active.remove(active.length - 1)
      else i += 1
    if shrunk != null then
      var k = 0
      while k < shrunk.length do
        addPassive(shrunk(k)) match
          case Some(empty) => return Some(empty)
          case None => ()
        k += 1
    None

  /** Normal-form `m` against the active positive unit equalities (the demodulators). Returns `m` unchanged
   *  when demodulation is off or nothing rewrites. At selection `active` does not yet contain the given, so
   *  the given never demodulates itself. */
  private def forwardDemodulate(m: Clause): Clause =
    if !forwardDemodulationOn || activeDemodulators.isEmpty then m
    else Demodulation.normalForm(bank, trail, bank.order, m, activeDemodulators.toArray)

  /** When `gc` is a new positive unit equality, rewrite the active clauses with it: each rewritten clause is
   *  removed from active and its replacement re-added via `addPassive`. Returns `Some(□)` on refutation. */
  private def backwardDemodulateStep(gc: Clause): Option[Clause] =
    if !backwardDemodulationOn || !isPosUnitEq(gc) then None
    else
      var pairs = Demodulation.backwardDemodulate(bank, trail, bank.order, gc, active)
      while pairs.nonEmpty do
        val (removed, replacement) = pairs.head
        removeFromActive(removed)
        addPassive(replacement) match
          case Some(empty) => return Some(empty)
          case None => ()
        pairs = pairs.tail
      None

  /** Remove the clause with `c`'s id from active (swap-with-last; active is unordered), keeping the
   *  demodulator set in sync. */
  private def removeFromActive(c: Clause): Unit =
    if isPosUnitEq(c) then removeDemodulatorsOf(c)
    var i = 0
    while i < active.length do
      if active(i).id == c.id then
        active(i) = active(active.length - 1)
        active.remove(active.length - 1)
        return
      i += 1

  /** Drop from `activeDemodulators` the rules whose source is the (removed) clause `c`. */
  private def removeDemodulatorsOf(c: Clause): Unit =
    var i = 0
    while i < activeDemodulators.length do
      if activeDemodulators(i).source.id == c.id then
        activeDemodulators(i) = activeDemodulators(activeDemodulators.length - 1)
        activeDemodulators.remove(activeDemodulators.length - 1)
      else i += 1

  /** Whether `c` is a positive unit equality (a demodulator candidate). */
  private def isPosUnitEq(c: Clause): Boolean =
    c.literals.length == 1 && bank.isPositive(c.literals(0)) &&
      bank.headSymbol(bank.atomOf(c.literals(0))) == EqualitySymbol

  /** Whether `lit`'s atom is an equality `s = t` (ordinary resolution/factoring skip these). */
  private def isEquality(lit: Literal): Boolean =
    bank.headSymbol(bank.atomOf(lit)) == EqualitySymbol

  /** σ-maximality after-check: in the (already σ-applied) factor `f`, the kept literal must be maximal --
   *  no other literal's atom is strictly KBO-greater than it. (Maximal, not strictly: the merged literal
   *  may have an equal twin.) */
  private def keptMaximal(f: Clause, keptIdx: Int): Boolean =
    val keptAtom: Term = bank.atomOf(f.literals(keptIdx))
    var k = 0
    while k < f.literals.length do
      if k != keptIdx && kbo.compare(bank.atomOf(f.literals(k)), keptAtom) == Cmp.Gt then return false
      k += 1
    true
