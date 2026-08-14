package lisa.automation.superposition

import Core.*

/**
 * θ-subsumption between clauses: the redundancy test that drives forward and backward
 * subsumption in the saturation loop.
 *
 * A clause `c` **subsumes** `d` iff there is a substitution `σ` such that `cσ ⊆ d` as a
 * multiset of literals -- i.e. each literal of `c` can be matched (same predicate, same
 * polarity, instantiating only `c`'s variables) onto a *distinct* literal of `d` under one
 * shared `σ`. Subsumption implies `c ⊨ d`, so a subsumed `d` is redundant and may be deleted
 * without affecting completeness (and, crucially for us, without any proof obligation: a
 * deleted clause never enters the empty clause's justification DAG).
 *
 * The test is built directly on the one-sided matcher ([[Core.Trail.matchLiteral]]): `c` is the
 * pattern in scope [[PatScope]] (its variables bind), `d` is the rigid target in scope
 * [[TgtScope]]. The two scopes keep the clauses' variable numbers distinct without renaming.
 *
 * Two layers of work, cheap-before-expensive:
 *
 *   1. [[sigSubsumes]] -- an O(1) necessary-condition pre-filter over the cached clause
 *      signature (size, polarity counts, weight, head-symbol fingerprint). It rejects the vast
 *      majority of non-subsuming pairs before any trail manipulation, and is *sound*: it never
 *      rejects a genuine subsumption (each condition is implied by `cσ ⊆ d`).
 *
 *   2. The matching search itself -- a unit fast path (no injectivity bookkeeping needed for a
 *      one-literal `c`), and otherwise an injective backtracking search over `c`'s literals,
 *      trying the **most constrained (heaviest) literal first** to prune early.
 *
 * [[subsumes]] is self-contained (it applies [[sigSubsumes]] internally) and leaves the trail
 * exactly as it found it on every path, so callers may invoke it freely without bracketing.
 */
object Subsumption:

  /** Scope of the (pattern) clause whose variables are instantiated by `σ`. */
  private inline val PatScope = 0

  /** Scope of the (rigid) target clause `d`; its variables never bind. */
  private inline val TgtScope = 1

  /**
   * Cheap, sound necessary-condition pre-filter for `c` subsuming `d`, using only the cached
   * clause signatures (no trail, no matching). All four conditions follow from `cσ ⊆ d`:
   *   - `c.size <= d.size`            -- the literal map is injective into `d`;
   *   - `c.posCount <= d.posCount` and `c.negCount <= d.negCount` -- matching preserves polarity;
   *   - `c.weight <= d.weight`        -- `weight(c) <= weight(cσ) <= weight(d)` (σ can only grow
   *                                      terms, and `cσ` is a sub-multiset of `d`);
   *   - `(c.predBits & d.predBits) == c.predBits` -- every head symbol of `c` (mod 64) also
   *                                      occurs in `d`.
   * Being only necessary, a `true` here must still be confirmed by [[subsumes]].
   */
  def sigSubsumes(c: Clause, d: Clause): Boolean =
    c.size <= d.size &&
      c.posCount <= d.posCount &&
      c.negCount <= d.negCount &&
      c.weight <= d.weight &&
      (c.predBits & d.predBits) == c.predBits

  /**
   * Whether `c` θ-subsumes `d`. Self-contained: applies [[sigSubsumes]] first, then searches for
   * an injective, polarity-preserving match of all of `c`'s literals onto distinct literals of
   * `d` under one shared substitution. The trail is restored to its entry state before
   * returning, on both the `true` and `false` paths.
   */
  def subsumes(bank: TermBank, trail: Trail, c: Clause, d: Clause): Boolean =
    if !sigSubsumes(c, d) then return false
    val cl: Array[Literal] = c.literals
    val dl: Array[Literal] = d.literals
    if cl.length == 0 then return true // the empty clause subsumes everything (□ ⊨ d)
    val s: Int = trail.save()
    val r: Boolean =
      if cl.length == 1 then matchesSome(bank, trail, cl(0), dl) // unit: injectivity is trivial
      else
        // try c's most constrained (heaviest -- most structure, fewest matches) literal first
        val order: Array[Int] = orderByWeightDesc(bank, cl)
        val used: Array[Boolean] = new Array[Boolean](dl.length)
        matchRec(bank, trail, cl, dl, order, used, 0)
    trail.restore(s)
    r

  /** Does the single pattern literal `lit` match *some* literal of `dl`? (Leaves bindings; the
   *  caller's [[subsumes]] restore cleans them.) */
  private def matchesSome(bank: TermBank, trail: Trail, lit: Literal, dl: Array[Literal]): Boolean =
    val lw: Int = bank.literalWeight(lit)
    var j = 0
    while j < dl.length do
      // weight skip (Check 1): `lit σ = dl(j)` forces `weight(dl(j)) >= weight(lit)`, so a lighter
      // target cannot match -- cheaper to reject than to set up and run `matchLiteral`.
      if bank.literalWeight(dl(j)) >= lw then
        val s: Int = trail.save()
        if trail.matchLiteral(lit, PatScope, dl(j), TgtScope) then return true
        trail.restore(s) // failed attempt may have left partial bindings
      j += 1
    false

  /**
   * Injective backtracking match: assign `c`'s literals (visited in `order`, position `k` onward)
   * to distinct, not-yet-`used` literals of `d` under one shared σ recorded on the trail. Returns
   * `true` with the witnessing bindings left on the trail (the top-level [[subsumes]] restores).
   */
  private def matchRec(bank: TermBank, trail: Trail, cl: Array[Literal], dl: Array[Literal], order: Array[Int], used: Array[Boolean], k: Int): Boolean =
    if k == order.length then true
    else
      val ci: Literal = cl(order(k))
      val ciw: Int = bank.literalWeight(ci) // Check 1: a matching target must weigh at least this
      val s: Int = trail.save()
      val nd: Int = dl.length
      var j = 0
      while j < nd do
        // Check 1 (see matchesSome): skip a target too light to match `ci`
        if !used(j) && bank.literalWeight(dl(j)) >= ciw then
          if trail.matchLiteral(ci, PatScope, dl(j), TgtScope) then
            used(j) = true
            if matchRec(bank, trail, cl, dl, order, used, k + 1) then return true
            used(j) = false
          trail.restore(s) // undo this attempt (failed match left partial bindings, or recursion failed)
        j += 1
      false

  /**
   * Subsumption resolution -- a *simplifying* resolution. If `side = C' ∨ L` and some literal `K` of `main`
   * has the **opposite** polarity to `L` under a one-sided σ with `Lσ = ¬K` **and** `C'σ ⊆ main \ {K}`
   * (the rest of `side` injectively matches the rest of `main`, σ binding only `side`'s variables), then
   * `main` is redundant given the shorter clause `main \ {K}`. Returns that clause; `None` otherwise. The
   * **unit case** (`|side| = 1`, so `C' = ∅` and the second condition is vacuous) is *unit deletion*.
   *
   * One-sidedness (matching, not unification) is the guard that makes this a *simplification* rather than a
   * generating resolution: σ leaves `main` rigid, so the resolvent's literals are a sub-multiset of
   * `main`'s and the resolvent subsumes `main`, so deleting `main` is sound. A two-sided unifier that bound
   * `main`'s variables would yield only an instance of `main`, which does not subsume it.
   *
   * The result is the canonicalised resolvent, an ordinary clause (`Justification.Resolution`, densely
   * renumbered, reconstruction-faithful) -- subsumption resolution needs **no** dedicated justification or
   * reconstruction step; the loop simply deletes `main` (deletion is reconstruction-free, like subsumption).
   *
   * **Why the [[subsumes]] gate.** A *longer* side can leave variables outside `L` free (`resolve`'s mgu binds
   * only `L`), so the built clause `C'σ₀ ∪ M'` need not entail `main`; we keep it **only when it `subsumes`
   * `main`**, else the deletion would break completeness (discard a clause a refutation needs). Conservative: it
   * misses SR steps whose `C'` carries extra variables (a complete version needs the full matcher σ + a
   * reconstruction, deferred; see `archive/PossibleOptimizations.md`).
   */
  def subsumptionResolutionResolvent(bank: TermBank, trail: Trail, side: Clause, main: Clause): Option[Clause] =
    // The size/weight/predicate conditions of [[sigSubsumes]] hold here too, and for the same reasons: `C'σ ⊆ M'`
    // and `Lσ = ¬K` put all of `side` into `main` up to polarity. Not `sigSubsumes` itself, since the polarity
    // counts do *not* carry over, since `L` matches a literal of the opposite sign.
    if side.size > main.size || side.weight > main.weight then return None
    if (side.predBits & main.predBits) != side.predBits then return None
    val sl: Array[Literal] = side.literals
    val ml: Array[Literal] = main.literals
    val unit: Boolean = sl.length == 1 // C' empty: the resolvent is `main \ {K}`, which always subsumes `main`
    var iL = 0
    while iL < sl.length do
      val aL: Term = bank.atomOf(sl(iL))
      val pL: Boolean = bank.isPositive(sl(iL))
      var iK = 0
      while iK < ml.length do
        if bank.isPositive(ml(iK)) != pL then // complementary candidate: L could resolve K away
          // cheap one-sided pre-check (necessary for the resolvent to subsume `main`); restore before resolve
          val s: Int = trail.save()
          val matched: Boolean = trail.matchTerm(aL, PatScope, bank.atomOf(ml(iK)), TgtScope)
          trail.restore(s)
          if matched then
            Inference.resolve(bank, trail, side, iL, main, iK) match
              case Some(raw) =>
                Inference.canonicalize(bank, raw) match
                  // keep `rc` and delete `main` only if `rc` entails `main` (completeness gate; see above)
                  case Some(rc) => if unit || subsumes(bank, trail, rc, main) then return Some(rc)
                  case None     => () // canonicalisation dropped it as a tautology: skip it (as `condense` does), never use raw
              case None => ()
        iK += 1
      iL += 1
    None

  /**
   * Condensation: replace `c` by an equivalent shorter clause when one exists. A *condensation* is a factor
   * `cσ` (two same-polarity literals unified and merged) that is strictly shorter than `c` and **subsumes**
   * it. A factor is an instance, so `c ⊨ cσ` already; the `subsumes` gate adds `cσ ⊨ c`, making them
   * equivalent, so replacing `c` by `cσ` is sound and completeness-preserving. (Without the gate the factor is
   * only a weaker instance, and deleting `c` would drop a constraint -- a completeness failure.)
   *
   * Returns the fully-condensed clause -- iterating, since one merge can expose another -- or `c` itself if it
   * is already condensed. The result is an ordinary factor (`Justification.Factoring`, chained when several
   * merges apply), so condensation needs no dedicated reconstruction. Unlike the generating factoring in the
   * loop, condensation is a *simplification*, so it is not restricted to selected or positive literals: it
   * tries every same-polarity pair.
   */
  def condense(bank: TermBank, trail: Trail, c: Clause): Clause =
    var cur: Clause = c
    var progress = true
    while progress do
      progress = false
      val cl: Array[Literal] = cur.literals
      var i = 0
      while i < cl.length && !progress do
        var j = i + 1
        while j < cl.length && !progress do
          // `factor` only merges same-polarity literals; pre-check avoids the call for the rest
          if bank.isPositive(cl(i)) == bank.isPositive(cl(j)) then
            Inference.factor(bank, trail, cur, i, j) match
              case Some(f) =>
                Inference.canonicalize(bank, f) match
                  // keep the (shorter) factor only when it subsumes `cur` -- then `cur ≡ factor`
                  case Some(fc) if subsumes(bank, trail, fc, cur) => cur = fc; progress = true
                  case _ => ()
              case None => ()
          j += 1
        i += 1
    cur

  /**
   * Indices `0 until lits.length` ordered by descending literal weight. Matching the heaviest (most specific)
   * literals first prunes the search: they have the fewest candidate targets, so a clash is found before
   * cheap, ambiguous literals fan the search out. Insertion sort -- clause literal counts are tiny, so this
   * beats a comparator-driven sort.
   */
  private def orderByWeightDesc(bank: TermBank, lits: Array[Literal]): Array[Int] =
    val n: Int = lits.length
    val order: Array[Int] = new Array[Int](n)
    var i = 0
    while i < n do
      order(i) = i
      i += 1
    var a = 1
    while a < order.length do
      val key: Int = order(a)
      val kw: Int = bank.literalWeight(lits(key))
      var b: Int = a - 1
      while b >= 0 && bank.literalWeight(lits(order(b))) < kw do
        order(b + 1) = order(b)
        b -= 1
      order(b + 1) = key
      a += 1
    order
