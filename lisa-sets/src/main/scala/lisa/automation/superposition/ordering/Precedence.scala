package lisa.automation.superposition
package ordering

import Core._

/**
 * How the KBO symbol precedences are generated, following E and Vampire. Each scheme computes the order once
 * from the symbol counts of the input clauses. The default makes frequent symbols small, so that terms
 * rewrite toward the common vocabulary and rare symbols are eliminated first.
 *
 * Every scheme gives distinct precedences, which KBO needs to stay total on ground terms: it returns `Inc`
 * for two distinct symbols of equal precedence.
 */
enum PrecedenceScheme:
  /**
   * Interning order (identity): the arbitrary baseline, kept for A/B comparison.
   */
  case Occurrence

  /**
   * Constants minimal, then more-frequent ⇒ smaller precedence; id tiebreak. The default (E `invfreqconstmin`
   *  / Vampire `frequency`, direction: frequent-small).
   */
  case InvFrequency

  /**
   * Higher arity ⇒ larger precedence; id tiebreak.
   */
  case Arity

  /**
   * Unary symbols largest (E `unary_first`), then by arity; id tiebreak.
   */
  case UnaryFirst

object Precedence:

  /**
   * Assign every symbol's precedence under `scheme`, from its occurrence count in `clauses`. Call once, after
   * the signature is interned and before saturation. It has to run this late: the default scheme ranks symbols
   * by how often they occur, so it needs every clause first. Doing so after the clauses are built is sound
   * because KBO reads the precedence live and caches only the weights, which are fixed at interning.
   * Idempotent for a fixed input.
   *
   * This is the only thing that changes the term ordering once terms exist, so it ends by clearing the one
   * cache built on the ordering ([[Order.invalidate]]). Everything downstream may then treat the ordering as
   * fixed, which is why nothing else stamps or re-checks it.
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
    bank.order.invalidate() // no verdict taken under the interning-order precedence may survive this

  /**
   * Accumulate every symbol occurrence in `t` (head + all subterms; variables carry no symbol).
   */
  private def countTerm(bank: TermBank, t: Term, count: Array[Long]): Unit =
    if !bank.isVar(t) then
      count(bank.headSymbol(t).code) += 1
      val ar = bank.arity(t)
      var i = 0
      while i < ar do { countTerm(bank, bank.arg(t, i), count); i += 1 }

  /**
   * Strict order: `true` iff `a` should get a **smaller** precedence than `b`. Fully broken by symbol id, so
   *  the induced order is total.
   */
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
