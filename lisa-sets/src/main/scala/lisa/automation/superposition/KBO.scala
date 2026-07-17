package lisa.automation.superposition

import Core.*

/** The four-valued outcome of a KBO comparison of two terms. */
enum Cmp:
  case Gt // strictly greater
  case Lt // strictly lesser
  case Eq // equal
  case Inc // incomparable

/**
 * The Knuth-Bendix ordering on concrete (fully built) terms of a [[TermBank]].
 *
 * This is the linear *tupling* algorithm of Bernd Löchner, "Things to Know when Implementing
 * KBO" (J. Automated Reasoning 36:289-310, 2006) -- specifically a port of E's recursive
 * `kbo6cmp`/`kbo6cmplex` (`cto_kbolin.c`, "CTKBO4-6"), which is also the basis of Vampire's
 * `KBO::State`. A single simultaneous traversal of the two terms accumulates:
 *
 *   - `wb`  : the weight balance `w(s) - w(t)`;
 *   - `vb`  : per-variable balance `#(x,s) - #(x,t)`, a dense array indexed by variable number;
 *   - `posCount` / `negCount`: how many variables have `vb > 0` / `< 0` (so the *variable
 *     condition* "`s` dominates `t` on every variable" is just `negCount == 0`, and the dual
 *     `posCount == 0`); these are maintained incrementally as `vb` is bumped.
 *
 * The lexicographic descent stops recursing at the first non-`Eq` argument and only sweeps the
 * remaining arguments to finish the balances (`accumulateBalance`), which is what makes the whole compare
 * linear rather than quadratic. The final outcome is resolved by weight, then top-symbol
 * precedence, then the saved lexicographic result, with the variable condition downgrading any
 * otherwise-decisive verdict to `Inc`.
 *
 * Three properties of our representation are exploited (without changing the result): the cached
 * per-term weight gives a ground/ground fast path and a no-descent `accumulateBalance` on ground subterms;
 * hash-consing makes `s == t` an O(1) identity test, so equal terms and equal arguments are
 * dispatched immediately.
 *
 * The accumulator state is reused across calls and reset at the start of each [[compare]];
 * an instance is therefore **not** thread-safe (like E's `OCB` and Vampire's `State`).
 *
 * Comparison is on terms that already share one variable namespace; comparing under a
 * substitution without materialising it (E's `DerefType` / Vampire's `AppliedTerm`) is left for
 * a later phase, as is the unidirectional "is-greater" fast path.
 */
final class KBO(val bank: TermBank):
  import Cmp.*

  private val signature: Signature = bank.signature

  // --- reused tupling state (reset at the start of every `compare`) -------------------------
  private var wb: Long = 0 // weight balance  w(s) - w(t)
  private var posCount: Int = 0 // number of variables with vb > 0
  private var negCount: Int = 0 // number of variables with vb < 0
  private var vb: Array[Int] = new Array[Int](16) // variable number -> balance #(x,s) - #(x,t)
  private var maxVar: Int = -1 // high-water mark of touched `vb` entries, so `reset` clears only [0..maxVar]

  /** Compare `s` and `t` under the KBO, returning `Gt`, `Lt`, `Eq`, or `Inc`. */
  def compare(s: Term, t: Term): Cmp =
    if s == t then Eq
    else if bank.isGround(s) && bank.isGround(t) then compareGround(s, t)
    else
      reset()
      kbocmp(s, t)

  /** Whether `s` is strictly greater than `t`. */
  def greater(s: Term, t: Term): Boolean = compare(s, t) == Gt

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
    if v >= vb.length then
      var nl: Int = vb.length * 2
      while nl <= v do nl *= 2
      vb = java.util.Arrays.copyOf(vb, nl)
    if v > maxVar then maxVar = v

  /** Clear the accumulators for a fresh comparison (only the touched `vb` prefix). */
  private def reset(): Unit =
    var i = 0
    while i <= maxVar do
      vb(i) = 0
      i += 1
    wb = 0
    posCount = 0
    negCount = 0
    maxVar = -1

  /**
   * Sweep one term into the accumulators with the given side (`lhs = true` adds to `s`, `false`
   * to `t`): add `±` each symbol's weight and bump the variable balance for each variable. A
   * ground subterm is folded in O(1) via its cached weight, with no descent.
   */
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



  // --- internals ----------------------------------------------------------------------------

  /**
   * Full comparison of two ground terms. With no variables the variable condition is vacuous, so
   * (when the precedence is total) the result is never `Inc`: at each level the cached weight
   * decides, then top-symbol precedence, then a lexicographic recurse on the arguments. This stays
   * entirely off the variable-balance machinery and needs no `reset`, reading the cached weights
   * directly -- the whole point of caching them. Precondition: `s` and `t` are ground, hence so is
   * every subterm reached by the recursion.
   */
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

  /**
   * The core comparison (Löchner's `tckbo`): compare `s` and `t`, returning the lexicographic
   * verdict for this position while updating the global `wb`/`vb`/`pos`/`neg` accumulators over
   * both subterms. Variable cases settle directly via the occurs check; both-compound cases
   * resolve by weight, then precedence, then the recursive lexicographic result.
   */
  private def kbocmp(s: Term, t: Term): Cmp =
    if s == t then Eq
    else
      // "Pacman" reduction: f(a) vs f(b) with the same unary head reduces to a vs b (the head's
      // weight cancels and carries no variables). Perfect sharing makes f(x) and f(y) the same
      // handle iff x and y are, so this preserves a != b (which holds here since s != t was handled
      // above) -- no equality check is needed in or after the loop.
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

  /**
   * Lexicographic comparison of the arguments of two terms with the same head symbol (hence the
   * same arity). Recurses on arguments in lockstep until the first non-`Eq` result, then merely
   * sweeps the remaining arguments into the balances. Identical arguments are skipped: being the
   * same handle, they contribute nothing to either balance.
   */
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



  
  /**
   * Validate that the signature's current weights and precedence make this an admissible KBO
   * (hence a reduction ordering). Returns `None` if admissible, or `Some(reason)` for the first
   * violation found: the variable weight must be positive, every constant must weigh at least the
   * variable weight, and a weight-zero unary symbol (if any) must be precedence-maximal.
   */
  def checkAdmissibility(): Option[String] =
    val varWeight: Int = Core.VariableWeight
    if varWeight <= 0 then Some(s"variable weight must be positive, got $varWeight")
    else
      // the (unique, when precedence is total) precedence-maximal symbol
      var maxInfo: Option[SymbolInfo] = None
      signature.symbols.foreach { info =>
        if maxInfo.isEmpty || signature.comparePrecedence(info, maxInfo.get) > 0 then maxInfo = Some(info)
      }
      signature.symbols.collectFirst {
        case info if info.arity == 0 && info.weight < varWeight =>
          s"constant ${info.name} has weight ${info.weight} < variable weight $varWeight"
        case info if info.arity == 1 && info.weight == 0 && !maxInfo.exists(m => signature.comparePrecedence(info, m) == 0) =>
          s"unary symbol ${info.name} of weight 0 must be precedence-maximal"
      }
