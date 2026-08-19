package lisa.automation.superposition

import Core.*

/** θ-subsumption, and the two simplifications built directly on it: subsumption resolution and condensation.
  * A clause `c` subsumes `d` when some `σ` maps `c`'s literals injectively onto literals of `d`.
  *
  * Two layers: [[sigSubsumes]], an O(1) filter over the cached clause signature, then an injective backtracking
  * search over `c`'s literals, heaviest first so that failure comes early, built on
  * [[Core.Trail.matchLiteral]] with `c` as pattern and `d` rigid, so neither needs renaming. [[subsumes]]
  * applies the filter itself and restores the trail on every path, so callers need not bracket it. */
object Subsumption:

  /** Scope of the (pattern) clause whose variables are instantiated by `σ`. */
  private inline val PatScope = 0

  /** Scope of the (rigid) target clause `d`; its variables never bind. */
  private inline val TgtScope = 1

  /** Cheap, sound pre-filter for `c` subsuming `d`, over the cached signatures alone (no trail, no matching).
    * All four conditions follow from `cσ ⊆ d`: sizes and polarity counts, `weight(c) <= weight(cσ) <= weight(d)`,
    * and every head symbol of `c` (mod 64) occurring in `d`. 
    * Being only necessary, a `true` must still be confirmed by [[subsumes]]. */
  def sigSubsumes(c: ClauseBody, d: ClauseBody): Boolean =
    c.size <= d.size &&
      c.posCount <= d.posCount &&
      c.negCount <= d.negCount &&
      c.weight <= d.weight &&
      (c.predBits & d.predBits) == c.predBits

  /** Whether `c` θ-subsumes `d`. Self-contained: applies [[sigSubsumes]] first, then searches for
    * an injective, polarity-preserving match of all of `c`'s literals onto distinct literals of
    * `d` under one shared substitution. The trail is restored to its entry state before returning. */
  def subsumes(bank: TermBank, trail: Trail, c: ClauseBody, d: ClauseBody): Boolean =
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
        /** Assign `c`'s literals from position `k` of `order` onward to distinct, not-yet-`used` literals of
          * `d` under one shared σ recorded on the trail. Returns `true` with the witnessing bindings left on
          * the trail, which the `restore` below cleans up. */
        def matchRec(k: Int): Boolean =
          if k == order.length then true
          else
            val ci: Literal = cl(order(k))
            val ciw: Int = bank.literalWeight(ci)
            val saved: Int = trail.save()
            val nd: Int = dl.length
            var j = 0
            while j < nd do
              if !used(j) && bank.literalWeight(dl(j)) >= ciw then // weight skip, as in `matchesSome`
                if trail.matchLiteral(ci, PatScope, dl(j), TgtScope) then
                  used(j) = true
                  if matchRec(k + 1) then return true
                  used(j) = false
                trail.restore(saved) // undo this attempt (failed match left partial bindings, or recursion failed)
              j += 1
            false
        matchRec(0)
    trail.restore(s)
    r

  /** Does the single pattern literal `lit` match *some* literal of `dl`? (Leaves bindings; the
   *  caller's [[subsumes]] restore cleans them.) */
  private def matchesSome(bank: TermBank, trail: Trail, lit: Literal, dl: Array[Literal]): Boolean =
    val lw: Int = bank.literalWeight(lit)
    var j = 0
    while j < dl.length do
      // weight skip: `lit σ = dl(j)` forces `weight(dl(j)) >= weight(lit)`, so a lighter target cannot
      // match -- cheaper to reject than to set up and run `matchLiteral`.
      if bank.literalWeight(dl(j)) >= lw then
        val s: Int = trail.save()
        if trail.matchLiteral(lit, PatScope, dl(j), TgtScope) then return true
        trail.restore(s) // failed attempt may have left partial bindings
      j += 1
    false

  /** Subsumption resolution. If `side = C' ∨ L` and some literal `main = C ∨ K` where there is `σ` such that
    * a matcher with `Lσ = ¬K` and `C'σ ⊆ main \ {K}`, then `main` is redundant given `main \ {K}`, which is
    * returned. The unit case, where `C'` is empty, is unit deletion. The result is an ordinary resolvent. */
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
      val wL: Int = bank.literalWeight(sl(iL)) // `Lσ = ¬K` forces `weight(K) >= weight(L)`: the weight skip again
      var iK = 0
      while iK < ml.length do
        // complementary candidate of sufficient weight: L could resolve K away
        if bank.isPositive(ml(iK)) != pL && bank.literalWeight(ml(iK)) >= wL then
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

  /** Replace `c` by a strictly shorter factor of itself that also subsumes it, iterating since one merge can
    * expose another, or return `c` unchanged. A factor is already an instance, so the subsumption check is what
    * makes the two equivalent and the replacement sound. Being a simplification, it is not restricted to
    * selected literals and tries every same-polarity pair. */
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
          Inference.factor(bank, trail, cur, i, j) match // `factor` itself rejects a mixed-polarity pair
            case Some(f) =>
              Inference.canonicalize(bank, f) match
                // keep the (shorter) factor only when it subsumes `cur` -- then `cur ≡ factor`
                case Some(fc) if subsumes(bank, trail, fc, cur) => cur = fc; progress = true
                case _ => ()
            case None => ()
          j += 1
        i += 1
    cur

  /** Indices `0 until lits.length` ordered by descending literal weight. Matching the heaviest (most specific)
    * literals first prunes the search: they have the fewest candidate targets, so a clash is found before
    * cheap, ambiguous literals fan the search out. Insertion sort -- clause literal counts are tiny, so this
    * beats a comparator-driven sort. */
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
