package lisa.automation.superposition

import Core.*

/**
 * Symbol-**precedence** generation schemes for the KBO term ordering (Phase-5 heuristics; see
 * `ProverHeuristics.md`). KBO gives each symbol two independent parameters — a *weight* and a *precedence*
 * (a total order on symbols). The precedence is the tiebreak when the weight balance is zero and drives the
 * lexicographic argument descent, so it decides how equations orient (which side rewrites to which), which
 * literals come out maximal, and thus the whole shape of the search.
 *
 * Our default precedence used to be the **interning (occurrence) order** — arbitrary and parse-order
 * dependent, the weak default E and Vampire both avoid. These schemes replace it with a generated order,
 * computed once from the input clauses' symbol-occurrence counts (both provers agree the right general
 * default is **frequent symbols small**, so terms rewrite *toward* the common vocabulary and rare symbols
 * are eliminated first).
 *
 * Every scheme produces a **total** order (distinct precedences), which KBO needs to stay total on ground
 * terms — [[KBO]] returns `Inc` on "equal precedence but distinct symbols".
 */
enum PrecedenceScheme:
  /** Interning order (identity) — the arbitrary baseline, kept for A/B comparison. */
  case Occurrence
  /** Constants minimal, then more-frequent ⇒ smaller precedence; id tiebreak. The default (E `invfreqconstmin`
   *  / Vampire `frequency`, direction: frequent-small). */
  case InvFrequency
  /** Higher arity ⇒ larger precedence; id tiebreak. */
  case Arity
  /** Unary symbols largest (E `unary_first`), then by arity; id tiebreak. */
  case UnaryFirst

object Precedence:

  /**
   * Overwrite every signature symbol's `precedence` per `scheme`, from symbol-occurrence counts over
   * `clauses` (the input clause set — all function/predicate symbols that will ever appear are present by
   * then). Call once, after the whole signature is interned and **before** saturation (precedence is read
   * live by [[KBO]]; term weights are cached from symbol *weights*, not precedence, so this is sound after
   * clause construction). Idempotent for a fixed input.
   */
  def assign(sig: Signature, bank: TermBank, clauses: Iterable[Clause], scheme: PrecedenceScheme): Unit =
    val count = new Array[Long](sig.size)
    val cit = clauses.iterator
    while cit.hasNext do
      val lits = cit.next().literals
      var i = 0
      while i < lits.length do { countTerm(bank, bank.atomOf(lits(i)), count); i += 1 }
    // ascending key ⇒ ascending precedence (rank 0 = smallest / "simplest")
    val ordered: Array[SymbolInfo] = sig.symbols.toArray.sortWith((a, b) => precedes(a, b, count, scheme))
    var rank = 0
    while rank < ordered.length do { ordered(rank).precedence = rank; rank += 1 }

  /** Accumulate every symbol occurrence in `t` (head + all subterms; variables carry no symbol). */
  private def countTerm(bank: TermBank, t: Term, count: Array[Long]): Unit =
    if !bank.isVar(t) then
      count(bank.headSymbol(t).code) += 1
      val ar = bank.arity(t)
      var i = 0
      while i < ar do { countTerm(bank, bank.arg(t, i), count); i += 1 }

  /** Strict order: `true` iff `a` should get a **smaller** precedence than `b`. Fully broken by symbol id, so
   *  the induced order is total. */
  private def precedes(a: SymbolInfo, b: SymbolInfo, count: Array[Long], scheme: PrecedenceScheme): Boolean =
    scheme match
      case PrecedenceScheme.Occurrence =>
        a.id.code < b.id.code
      case PrecedenceScheme.InvFrequency =>
        val aConst = a.arity == 0; val bConst = b.arity == 0
        if aConst != bConst then aConst //                       constants minimal
        else
          val fa = count(a.id.code); val fb = count(b.id.code)
          if fa != fb then fa > fb //                            more frequent ⇒ smaller
          else a.id.code < b.id.code
      case PrecedenceScheme.Arity =>
        if a.arity != b.arity then a.arity < b.arity //          lower arity smaller
        else a.id.code < b.id.code
      case PrecedenceScheme.UnaryFirst =>
        val aUnary = a.arity == 1; val bUnary = b.arity == 1
        if aUnary != bUnary then bUnary //                       unary largest ⇒ non-unary precedes unary
        else if a.arity != b.arity then a.arity < b.arity
        else a.id.code < b.id.code
