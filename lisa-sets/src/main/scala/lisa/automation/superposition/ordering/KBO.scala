package lisa.automation.superposition
package ordering

import Core.*

/** The four-valued outcome of a KBO comparison of two terms. */
enum Cmp:
  case Gt // strictly greater
  case Lt // strictly lesser
  case Eq // equal
  case Inc // incomparable

/** The Knuth-Bendix ordering on terms of a [[TermBank]], which must already share one variable namespace.
  *
  * Löchner's linear tupling algorithm ("Things to Know when Implementing KBO"), ported
  * from E. One traversal of both terms accumulates the weight balance and, per
  * variable, the occurrence balance, plus how many variables are unbalanced each way, so the variable condition
  * reduces to a counter being zero. The lexicographic descent recurses only to the first differing argument and
  * sweeps the rest into the balances, which is what keeps it linear.
  *
  * The accumulators are reused between calls, so an instance is not thread-safe. */
final class KBO(val bank: TermBank):
  import Cmp.*

  private val signature: Signature = bank.signature

  // --- reused tupling state (reset at the start of every `compare`) ---------------------------------------
  private var wb: Long = 0 // weight balance  w(s) - w(t)
  private var posCount: Int = 0 // number of variables with vb > 0
  private var negCount: Int = 0 // number of variables with vb < 0
  private var vb: Array[Int] = new Array[Int](16) // variable number -> balance #(x,s) - #(x,t)
  private var maxVar: Int = -1 // high-water mark of touched `vb` entries, so `reset` clears only [0..maxVar]

  def compare(s: Term, t: Term): Cmp =
    if s == t then Eq
    else if bank.isGround(s) && bank.isGround(t) then compareGround(s, t)
    else
      reset()
      kbocmp(s, t)

    /** Record an occurrence of variable `v` on the left, updating the balance and the pos/neg counts. */
  private def incVb(v: Int): Unit =
    ensureVb(v)
    val old: Int = vb(v)
    vb(v) = old + 1
    if old == 0 then posCount += 1
    else if old == -1 then negCount -= 1
    wb += Core.VariableWeight

  /** Record an occurrence of variable `v` on the right, updating the balance and the pos/neg counts. */
  private def decVb(v: Int): Unit =
    ensureVb(v)
    val old: Int = vb(v)
    vb(v) = old - 1
    if old == 0 then negCount += 1
    else if old == 1 then posCount -= 1
    wb -= Core.VariableWeight

  /** Ensure `vb` can index `v`, and extend the reset high-water mark to cover it. */
  private def ensureVb(v: Int): Unit =
    if v >= vb.length then // `vb.length` is a power of two, so this is the next one above `v`, at least twice as long
      vb = java.util.Arrays.copyOf(vb, Integer.highestOneBit(v) << 1)
    if v > maxVar then maxVar = v

  /** Clear the accumulators for a fresh comparison (only the touched `vb` prefix). */
  private def reset(): Unit =
    java.util.Arrays.fill(vb, 0, maxVar + 1, 0) // a no-op when `maxVar` is -1
    wb = 0
    posCount = 0
    negCount = 0
    maxVar = -1

  /** Sweep one term into the accumulators with the given side (`lhs = true` adds to `s`, `false`
    * to `t`): add `±` each symbol's weight and bump the variable balance for each variable. A
    * ground subterm is folded in O(1) via its cached weight, with no descent. */
  private def accumulateBalance(t: Term, lhs: Boolean): Unit =
    if bank.isGround(t) then
      val w: Int = bank.weight(t)
      if lhs then wb += w else wb -= w
    else if bank.isVar(t) then
      if lhs then incVb(bank.varNum(t).num) else decVb(bank.varNum(t).num)
    else
      val sw: Int = signature.info(bank.headSymbol(t)).weight
      if lhs then wb += sw else wb -= sw
      val n: Int = bank.arity(t)
      var i = 0
      while i < n do
        accumulateBalance(bank.arg(t, i), lhs)
        i += 1



  // --- internals ------------------------------------------------------------------------------------------

  /** Full comparison of two ground terms. With no variables the variable condition is vacuous, so
    * (when the precedence is total) the result is never `Inc`: at each level the cached weight
    * decides, then top-symbol precedence, then a lexicographic recurse on the arguments.
    * Precondition: `s` and `t` are ground. */
  private def compareGround(s: Term, t: Term): Cmp =
    if s == t then Eq
    else
      val ws: Int = bank.weight(s)
      val wt: Int = bank.weight(t)
      if ws > wt then Gt
      else if ws < wt then Lt
      else
        val fa: Symbol = bank.headSymbol(s)
        val fb: Symbol = bank.headSymbol(t)
        val prec: Int = signature.comparePrecedence(fa, fb)
        if prec > 0 then Gt
        else if prec < 0 then Lt
        else if fa != fb then Inc // equal precedence but distinct symbols (precedence not total)
        else
          // same symbol, hence same arity: lexicographic comparison of the arguments
          val n: Int = bank.arity(s)
          var res: Cmp = Eq
          var i = 0
          while i < n && res == Eq do
            res = compareGround(bank.arg(s, i), bank.arg(t, i))
            i += 1
          res

  /** The core comparison: compare `s` and `t`, returning the lexicographic
    * verdict for this position while updating the global `wb`/`vb`/`pos`/`neg` accumulators over
    * both subterms. Variable cases settle directly via the occurs check; both-compound cases
    * resolve by weight, then precedence, then the recursive lexicographic result. */
  private def kbocmp(s: Term, t: Term): Cmp =
    if s == t then Eq
    else
      // Special case: f(a) vs f(b) with the same unary head reduces to a vs b (the head's
      // weight cancels and carries no variables). No equality check is needed in or after the loop.
      var a: Term = s
      var b: Term = t
      while bank.arity(a) == 1 && bank.headSymbol(a) == bank.headSymbol(b) do
        a = bank.arg(a, 0)
        b = bank.arg(b, 0)
      val aVar: Boolean = bank.isVar(a)
      val bVar: Boolean = bank.isVar(b)
      if aVar && bVar then
        // two distinct variables: balance them and report incomparable
        incVb(bank.varNum(a).num)
        decVb(bank.varNum(b).num)
        Inc
      else if aVar then
        // X vs t : X < t iff X occurs in t (then t is strictly heavier and dominates on X)
        val x: Variable = bank.varNum(a)
        accumulateBalance(b, false)
        incVb(x.num)
        if bank.containsVar(b, x) then Lt else Inc
      else if bVar then
        // s vs Y : s > Y iff Y occurs in s
        val y: Variable = bank.varNum(b)
        accumulateBalance(a, true)
        decVb(y.num)
        if bank.containsVar(a, y) then Gt else Inc
      else
        val fa: Symbol = bank.headSymbol(a)
        val fb: Symbol = bank.headSymbol(b)
        // This traversal is what fills in `wb`/`posCount`/`negCount` over both subterms
        val lex: Cmp =
          if fa == fb then kbocmplex(a, b)
          else
            accumulateBalance(a, true)
            accumulateBalance(b, false)
            Inc
        // safe to read the balances now: the subtree has been fully accumulated above
        val gOrN: Cmp = if negCount != 0 then Inc else Gt
        val lOrN: Cmp = if posCount != 0 then Inc else Lt
        if wb > 0 then gOrN
        else if wb < 0 then lOrN
        else
          val prec: Int = signature.comparePrecedence(fa, fb)
          if prec > 0 then gOrN
          else if prec < 0 then lOrN
          else if fa != fb then Inc // equal precedence but distinct symbols (precedence not total)
          else
            lex match
              case Eq => Eq
              case Gt => gOrN
              case Lt => lOrN
              case Inc => Inc

  /** Lexicographic comparison of the arguments of two terms with the same head symbol (hence the
    * same arity). Recurses on arguments in lockstep until the first non-`Eq` result, then merely
    * sweeps the remaining arguments into the balances. Identical arguments are skipped: being the
    * same handle, they contribute nothing to either balance. */
  private def kbocmplex(s: Term, t: Term): Cmp =
    var res: Cmp = Eq
    val n: Int = bank.arity(s)
    var i = 0
    while i < n do
      val si: Term = bank.arg(s, i)
      val ti: Term = bank.arg(t, i)
      if si == ti then () // identical argument: no net contribution, lex result unchanged
      else if res == Eq then res = kbocmp(si, ti)
      else
        accumulateBalance(si, true)
        accumulateBalance(ti, false)
      i += 1
    res



  
  /** Whether the signature's current weights and precedence make this an admissible KBO, and so a reduction
    * ordering. `None` if they do, otherwise the first violation: the variable weight must be positive, every
    * constant must weigh at least that, and a weight-zero unary symbol must be precedence-maximal.
    * Asserted once per problem by [[Bridge.solve]].*/
  private[automation] def checkAdmissibility(): Option[String] =
    val varWeight: Int = Core.VariableWeight
    if varWeight <= 0 then Some(s"variable weight must be positive, got $varWeight")
    else
      // the (unique, when precedence is total) precedence-maximal symbol
      val maxInfo: Option[SymbolInfo] =
        signature.symbols.reduceOption((a, b) => if signature.comparePrecedence(b, a) > 0 then b else a)
      signature.symbols.collectFirst {
        case info if info.arity == 0 && info.weight < varWeight =>
          s"constant ${info.name} has weight ${info.weight} < variable weight $varWeight"
        case info if info.arity == 1 && info.weight == 0 && !maxInfo.exists(m => signature.comparePrecedence(info, m) == 0) =>
          s"unary symbol ${info.name} of weight 0 must be precedence-maximal"
      }
