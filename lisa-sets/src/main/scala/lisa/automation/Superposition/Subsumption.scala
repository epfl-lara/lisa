package lisa.automation.superposition

import Core.*

/**
 * θ-subsumption between clauses: the redundancy test that drives forward and backward
 * subsumption in Phase 2.
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
        // weight skip (Check 1): skip targets too light to match `ci` before paying for `matchLiteral`
        if !used(j) && bank.literalWeight(dl(j)) >= ciw then
          if trail.matchLiteral(ci, PatScope, dl(j), TgtScope) then
            used(j) = true
            if matchRec(bank, trail, cl, dl, order, used, k + 1) then return true
            used(j) = false
          trail.restore(s) // undo this attempt (failed match left partial bindings, or recursion failed)
        j += 1
      false

  /**
   * Unit deletion -- the unit case of subsumption resolution. If `unit` is a one-literal clause `{L}` and
   * some literal `K` of `main` has the **opposite** polarity with `atom(L)` *matching* `atom(K)`
   * one-sidedly (so `Lσ = ¬K` with σ binding only the unit's variables), then `main` is redundant given
   * the shorter clause `main \ {K}`. Returns that clause; `None` if no such `K` exists.
   *
   * The one-sided **match** (not full unification) is the guard that makes this a *simplification*: it
   * forces the resolvent's literals to be a sub-multiset of `main`'s (σ leaves `main` rigid), so the
   * resolvent subsumes `main` and deleting `main` is sound. A two-sided unifier that bound `main`'s
   * variables would instead be a *generating* resolution, whose resolvent is only an instance of `main`
   * and does **not** subsume it.
   *
   * The result is built via [[Inference.resolve]], so it carries an ordinary `Justification.Resolution`
   * (densely renumbered, reconstruction-faithful) -- unit deletion needs **no** dedicated justification or
   * reconstruction step; the loop simply deletes `main` (deletion is reconstruction-free, like subsumption).
   */
  def unitDeletionResolvent(bank: TermBank, trail: Trail, unit: Clause, main: Clause): Option[Clause] =
    if unit.size != 1 then return None
    val l: Literal = unit.literals(0)
    // O(1) pre-filter: `K` must share `L`'s predicate (so `unit`'s single predicate bit must occur in
    // `main`) and have the opposite polarity (so `main` must hold a literal of that polarity).
    if (unit.predBits & main.predBits) == 0L then return None
    val pL: Boolean = bank.isPositive(l)
    if pL then { if main.negCount == 0 then return None }
    else if main.posCount == 0 then return None
    val aL: Term = bank.atomOf(l)
    val dl: Array[Literal] = main.literals
    var j = 0
    while j < dl.length do
      val k: Literal = dl(j)
      if bank.isPositive(k) != pL then // complementary polarity: a candidate to resolve away
        val s: Int = trail.save()
        val matched: Boolean = trail.matchTerm(aL, PatScope, bank.atomOf(k), TgtScope)
        trail.restore(s)
        // build via resolve (re-unifies; here the mgu equals the matcher, so it yields `main \ {K}`)
        if matched then return Inference.resolve(bank, trail, unit, 0, main, j)
      j += 1
    None

  /**
   * Indices `0 until lits.length` ordered by descending literal weight. Matching the heaviest
   * (most specific) literals first prunes the search: they have the fewest candidate targets, so
   * a clash is found before cheap, ambiguous literals fan the search out. Insertion sort -- clause
   * literal counts are tiny, so this beats a comparator-driven sort and allocates nothing extra.
   */
  private def orderByWeightDesc(bank: TermBank, lits: Array[Literal]): Array[Int] =
    val n: Int = lits.length
    val order: Array[Int] = new Array[Int](n)
    var i = 0
    while i < n do
      order(i) = i
      i += 1
    var a = 1
    while a < n do
      val key: Int = order(a)
      val kw: Int = bank.literalWeight(lits(key))
      var b: Int = a - 1
      while b >= 0 && bank.literalWeight(lits(order(b))) < kw do
        order(b + 1) = order(b)
        b -= 1
      order(b + 1) = key
      a += 1
    order
