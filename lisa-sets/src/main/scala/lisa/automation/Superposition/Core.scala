package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.{Int2IntOpenCustomHashMap, Int2IntOpenHashMap, IntHash, IntOpenHashSet}

import scala.collection.mutable
import scala.util.hashing.MurmurHash3

/**
 * Phase 0 core datastructures for the superposition prover: the symbol signature, a
 * hash-consed term bank backed by a single flat arena, packed literals, and clauses.
 *
 * The whole engine is built around opaque integer references:
 *   - a `Term` is an offset into the [[TermBank]]'s flat `Array[Long]` arena;
 *   - a `Literal` packs an atom term together with a polarity bit;
 *   - symbol codes are dense non-negative ints handed out by a [[Signature]].
 *
 * Variables are encoded directly in the term's functor field as a negative number, so no
 * separate cell type is needed (the E/LADR trick). Free-variable information is cached as
 * a 63-bit mask on every term, exact for variables `0..62` and OR-ed up from children;
 * bit 63 is an overflow marker meaning "some variable numbered >= 63 occurs here, fall
 * back to traversal". A term is ground iff its mask is `0`.
 *
 * Everything lives inside this object so that the opaque types are transparent to the
 * engine (they are abstract `Int`/`Long`s to outside code, e.g. tests).
 */
object Core:

  /** A reference to a term: the offset of its record in a [[TermBank]]'s arena. */
  opaque type Term = Int

  /** A literal: an atom [[Term]] together with a polarity, packed as `(atom << 1) | sign`. */
  opaque type Literal = Long

  /** A symbol code as handed out by a [[Signature]] (always `>= 0`); this is what a term stores as its head. */
  opaque type Symbol = Int

  /** A variable's number (`>= 0`); distinct from a [[Symbol]] at the type level, though both are `Int` at runtime. */
  opaque type Variable = Int

  /** Construct a [[Variable]] from its (non-negative) number. */
  inline def Variable(num: Int): Variable = num

  extension (v: Variable) inline def num: Int = v
  extension (f: Symbol) inline def code: Int = f

  /**
   * By convention the equality predicate is reserved as the arity-2 symbol with code `0` (i.e.
   * interned first in the problem signature). Recognising it is needed for selection (preferring
   * negative equalities) and, later, for superposition.
   */
  val EqualitySymbol: Symbol = 0

  /** A unification scope (`0` or `1`): which of the two clauses a variable belongs to. A transparent alias, purely documentary. */
  type Scope = Int

  /** Default Knuth-Bendix weight given to a freshly interned symbol. */
  val defaultSymbolWeight: Int = 1

  /**
   * The data for one interned symbol: immutable identity (`name`, `arity`, kind) and the
   * mutable ordering parameters used by KBO (`weight` and `precedence`). One instance is
   * allocated per distinct symbol. Terms refer to a symbol by its integer [[Symbol]] code
   * (`id`), so the hot paths index an array of these rather than dereferencing the object.
   */
  final class SymbolInfo private[Core] (val id: Symbol, val name: String, val arity: Int, val isPredicate: Boolean):
    var weight: Int = defaultSymbolWeight
    var precedence: Int = id
    override def toString: String = s"$name/$arity"

  // -----------------------------------------------------------------------------------------
  // Signature
  // -----------------------------------------------------------------------------------------

  /**
   * Interns function and predicate symbols into dense non-negative codes, and stores the
   * per-symbol data needed by KBO: a Knuth-Bendix weight and a precedence rank.
   *
   * A `(name, arity)` pair denotes a unique symbol, so `f/2` and `f/3` are distinct.
   * Predicates and functions share the same code space but are tagged via [[isPredicate]].
   * The default precedence is the interning order; both weight and precedence can be
   * reassigned afterwards (e.g. once the whole problem signature is known).
   */
  final class Signature:
    private val infos: mutable.ArrayBuffer[SymbolInfo] = mutable.ArrayBuffer.empty[SymbolInfo]
    private val index: mutable.HashMap[(String, Int), Symbol] = mutable.HashMap.empty[(String, Int), Symbol]

    /** Intern `(name, arity)`, returning its (stable) symbol code. */
    def intern(name: String, arity: Int, isPredicate: Boolean): Symbol =
      index.getOrElseUpdate(
        (name, arity), {
          val info: SymbolInfo = new SymbolInfo(infos.length, name, arity, isPredicate)
          infos += info
          info.id
        }
      )

    /** Number of distinct symbols interned so far. */
    def size: Int = infos.length

    /** The full record for symbol `f`; access its fields directly, storing it in a val when several are needed. */
    def info(f: Symbol): SymbolInfo = infos(f)

    /** Compare two symbols by precedence: negative if `f < g`, positive if `f > g`, `0` if equal. */
    def comparePrecedence(f: Symbol, g: Symbol): Int = Integer.compare(infos(f).precedence, infos(g).precedence)
    def comparePrecedence(f: SymbolInfo, g: SymbolInfo): Int = Integer.compare(f.precedence, g.precedence)

    /** All interned symbols, in code order (read-only; for admissibility checks and diagnostics). */
    def symbols: Iterator[SymbolInfo] = infos.iterator

  // -----------------------------------------------------------------------------------------
  // Term bank (flat arena + offset-keyed hash-consing)
  // -----------------------------------------------------------------------------------------

  /** Variable weight used by KBO; cached into each term's total weight at construction. */
  inline val VariableWeight = 1

  /** Overflow bit of a free-variable mask: set when some variable numbered `>= 63` occurs. */
  val FvOverflow: Long = 1L << 63

  /**
   * A hash-consed store of terms in a single flat arena. The arena is one growable
   * `Array[Long]`; every term is written as a contiguous record and a [[Term]] is just the
   * offset of that record. This is the AoS layout, but with all terms concatenated into one array and offsets used in
   * place of machine pointers.
   *
   * Record layout for a term at offset `p` (`n == arity`):
   * {{{
   *   mem(p + 0) = (functor & 0xFFFFFFFFL) | (n.toLong << 32)   // functor (<0 = var) + arity
   *   mem(p + 1) = free-variable mask
   *   mem(p + 2) = total KBO weight (low 32 bits)
   *   mem(p + 3 .. p + 2 + n) = the n child offsets
   * }}}
   *
   * Hash-consing uses a fastutil `Int2IntOpenCustomHashMap` keyed on term offsets, with an
   * [[IntHash.Strategy]] that hashes and compares a key by reading the record it points at,
   * so no key object is ever materialised. Interning is write-first: a candidate record is
   * appended at the bump pointer so it can be hashed/compared by offset like any stored
   * entry; on a hit the bump pointer is rewound and the stored offset returned, on a miss
   * the candidate offset is kept and inserted (mapping it to itself).
   */
  final class TermBank(val signature: Signature):

    private inline val HeaderWords = 3

    // --- arena ----------------------------------------------------------------------------
    private var mem: Array[Long] = new Array[Long](1024)
    private var end: Int = 0 // bump pointer: next free arena slot

    // --- hash-consing: fastutil map keyed on term content via a custom strategy -----------
    private val internStrategy: IntHash.Strategy = new IntHash.Strategy {
      def hashCode(t: Int): Int = hashOf(t)
      def equals(a: Int, b: Int): Boolean = equalRecords(a, b)
    }

    // maps a term offset to the canonical offset of its (content-)equal term
    private val intern: Int2IntOpenCustomHashMap =
      val m: Int2IntOpenCustomHashMap = new Int2IntOpenCustomHashMap(internStrategy)
      m.defaultReturnValue(-1)
      m

    private var clauseCounter: Int = 0

    /** The literal-selection strategy applied by [[Clause.select]] at activation; swap to plug in a policy. */
    var selector: LiteralSelector = BestLiteralSelector

    /** Number of distinct terms stored. */
    def size: Int = intern.size

    // --- constructors ---------------------------------------------------------------------

    /** The shared term for variable number `v` (`v >= 0`). */
    def mkVar(v: Variable): Term =
      require(v >= 0, s"variable number must be non-negative, got $v")
      ensureMem(HeaderWords)
      val p: Int = end
      mem(p) = encodeVar(v).toLong & 0xFFFFFFFFL // arity 0, so high word is 0
      mem(p + 1) = varBit(v)
      mem(p + 2) = VariableWeight.toLong
      end = p + HeaderWords
      internCandidate(p)

    /** A nullary symbol application, i.e. a constant. */
    def mkConst(f: Symbol): Term = mkApp(f, EmptyArgs)

    /** Apply symbol `f` to `children`. The array is read but not retained. */
    def mkApp(f: Symbol, children: Array[Term]): Term =
      require(f >= 0, s"symbol code must be non-negative, got $f")
      val info: SymbolInfo = signature.info(f)
      val n: Int = children.length
      require(n == info.arity, s"arity mismatch for ${info.name}: expected ${info.arity}, got $n")
      ensureMem(HeaderWords + n)
      val p: Int = end
      var mask = 0L
      var w: Int = info.weight
      var i = 0
      while i < n do
        val c: Term = children(i)
        mask |= mem(c + 1)
        w += mem(c + 2).toInt
        mem(p + HeaderWords + i) = c.toLong
        i += 1
      mem(p) = (f.toLong & 0xFFFFFFFFL) | (n.toLong << 32)
      mem(p + 1) = mask
      mem(p + 2) = w.toLong & 0xFFFFFFFFL
      end = p + HeaderWords + n
      internCandidate(p)

    // --- accessors ------------------------------------------------------------------------

    /** Raw functor field: `< 0` for variables, the symbol code otherwise. */
    inline def functor(t: Term): Int = mem(t).toInt // low 32 bits, sign-extended

    inline def isVar(t: Term): Boolean = functor(t) < 0

    /** Variable number of a variable term (undefined for non-variables). */
    inline def varNum(t: Term): Variable = decodeVar(functor(t))

    /** Head symbol of a compound/constant term (undefined for variables). */
    inline def headSymbol(t: Term): Symbol = functor(t)

    /** Number of arguments (`0` for variables and constants). */
    inline def arity(t: Term): Int = (mem(t) >>> 32).toInt

    /** The `i`-th argument of `t`. */
    inline def arg(t: Term, i: Int): Term = mem(t + HeaderWords + i).toInt

    /** A fresh array with the children of `t`. */
    def args(t: Term): Array[Term] =
      val n: Int = arity(t)
      val out: Array[Term] = new Array[Term](n)
      var i = 0
      while i < n do
        out(i) = mem(t + HeaderWords + i).toInt
        i += 1
      out

    /** Cached total KBO weight of `t`. */
    inline def weight(t: Term): Int = mem(t + 2).toInt

    /** Cached free-variable mask of `t` (see the object docs for the encoding). */
    inline def freeVarMask(t: Term): Long = mem(t + 1)

    /** A term is ground iff it has no free variables. */
    inline def isGround(t: Term): Boolean = freeVarMask(t) == 0L

    /** Whether variable number `v` occurs in `t`; exact via the mask, with a traversal fallback for `v >= 63`. */
    def containsVar(t: Term, v: Variable): Boolean =
      val m: Long = freeVarMask(t)
      if v < 63 then (m & (1L << v)) != 0L
      else if m == 0L then false
      else traverseContains(t, v)

    /** The smallest variable number occurring in `t`, or `-1` if `t` is ground; needs a traversal if only overflow vars occur. */
    def firstVar(t: Term): Variable =
      val m: Long = freeVarMask(t)
      val low: Long = m & ~FvOverflow
      if low != 0L then java.lang.Long.numberOfTrailingZeros(low)
      else if m == 0L then -1
      else traverseFirstVar(t, Int.MaxValue)

    private def traverseContains(t: Term, v: Variable): Boolean =
      if isVar(t) then varNum(t) == v
      else
        val n: Int = arity(t)
        var i = 0
        while i < n do
          // recurse via containsVar so each child's mask prunes subtrees with no var >= 63
          if containsVar(arg(t, i), v) then return true
          i += 1
        false

    private def traverseFirstVar(t: Term, best: Int): Int =
      if isVar(t) then math.min(best, varNum(t))
      else
        val n: Int = arity(t)
        var b: Int = best
        var i = 0
        while i < n do
          val child: Term = arg(t, i)
          if !isGround(child) then b = traverseFirstVar(child, b) // skip ground subtrees (no variables)
          i += 1
        b

    // --- literals -------------------------------------------------------------------------

    /** Build a literal from an atom and a polarity. */
    def mkLiteral(atom: Term, positive: Boolean): Literal = (atom.toLong << 1) | (if positive then 1L else 0L)

    /** The atom term underlying a literal. */
    def atomOf(l: Literal): Term = (l >>> 1).toInt

    def isPositive(l: Literal): Boolean = (l & 1L) == 1L
    def isNegative(l: Literal): Boolean = (l & 1L) == 0L

    /** Flip the polarity of a literal. */
    def negate(l: Literal): Literal = l ^ 1L

    /** Cached weight of a literal (its atom's weight). */
    def literalWeight(l: Literal): Int = weight(atomOf(l))

    // --- clauses --------------------------------------------------------------------------

    /**
     * Build a clause directly from `lits`, taking ownership of the array. This is a dumb
     * constructor (as in E/Vampire): it does not deduplicate, sort, or drop tautologies --
     * those are normalisation/simplification steps applied separately in the loop. It only
     * caches the clause weight (sum of literal weights) and assigns a fresh id. The empty
     * clause (`Array.empty`) denotes falsity.
     */
    def mkClause(lits: Array[Literal], justification: Justification = Justification.Input): Clause =
      var w = 0
      var i = 0
      while i < lits.length do
        w += literalWeight(lits(i))
        i += 1
      val id: Int = clauseCounter
      clauseCounter += 1
      val age: Int = justification match
        case Justification.Input => 0
        case Justification.Resolution(l, _, r, _) => math.max(l.age, r.age) + 1
        case Justification.Factoring(p, _, _) => p.age + 1
      new Clause(lits, w, id, justification, age)

    // --- internals ------------------------------------------------------------------------

    /**
     * Look the record freshly written at offset `p` up in the hash-cons table. If an equal
     * record already exists, rewind the bump pointer (discarding `p`) and return it;
     * otherwise keep `p` and insert it.
     */
    private def internCandidate(p: Term): Term =
      // putIfAbsent hashes/compares `p` against stored offsets via the arena in a single probe:
      // it inserts `(p, p)` and returns `-1` when absent, else returns the stored canonical offset.
      val existing: Term = intern.putIfAbsent(p, p)
      if existing != -1 then
        end = p // rewind: discard the candidate we just wrote
        existing
      else p

    /**
     * Hash a term by its identifying words (functor + arity, then children), using the
     * standard `MurmurHash3` mixing. The incremental `mix`/`finalizeHash` API is used so the
     * words are folded straight out of the arena, without materialising an array. This is the
     * same protocol as `scala.util.hashing.MurmurHash3.productHash` (a `mix` per element,
     * seeded with `productSeed`, then `finalizeHash`), just reading from the arena in place.
     */
    private def hashOf(t: Term): Int =
      val header: Long = mem(t)
      val n: Int = (header >>> 32).toInt
      var h: Int = MurmurHash3.productSeed
      h = MurmurHash3.mix(h, header.toInt) // functor (low 32 bits)
      h = MurmurHash3.mix(h, n) // arity (high 32 bits)
      var i = 0
      while i < n do
        h = MurmurHash3.mix(h, mem(t + HeaderWords + i).toInt)
        i += 1
      MurmurHash3.finalizeHash(h, n + 2)

    /** Structural equality of two records by reading the arena (functor+arity, then children). */
    private def equalRecords(a: Term, b: Term): Boolean =
      if mem(a) != mem(b) then false // packs functor + arity, so this compares both at once
      else
        val n: Int = (mem(a) >>> 32).toInt
        var i = 0
        while i < n do
          if mem(a + HeaderWords + i) != mem(b + HeaderWords + i) then return false
          i += 1
        true

    private def ensureMem(extra: Int): Unit =
      if end + extra > mem.length then
        var nl: Int = mem.length * 2
        while nl < end + extra do nl *= 2
        mem = java.util.Arrays.copyOf(mem, nl)

  // -----------------------------------------------------------------------------------------
  // Literal selection
  // -----------------------------------------------------------------------------------------

  /**
   * A pluggable literal-selection strategy. Given a clause's literals it returns the indices
   * selected for inference -- **one or many**. Only selected literals are used as resolution /
   * factoring partners: by Bachmair-Ganzinger, selecting a negative literal restricts a clause to
   * that literal, while selecting (maximal) positive literals keeps it complete. A strategy that
   * needs the ordering (e.g. maximal-literal selection) can be a class capturing a [[KBO]]; the
   * signature stays the same. Indices are into the literal array as stored, which is never
   * reordered, so they remain valid as parent positions for proof reconstruction.
   */
  trait LiteralSelector:
    def select(bank: TermBank, literals: Array[Literal]): Array[Int]

  /** Selects the first negative literal if any, else the first literal (one literal); empty for `□`. */
  object FirstNegativeSelector extends LiteralSelector:
    def select(bank: TermBank, literals: Array[Literal]): Array[Int] =
      if literals.isEmpty then EmptySelection
      else
        var i = 0
        while i < literals.length do
          if bank.isNegative(literals(i)) then return Array(i)
          i += 1
        Array(0)

  /** Selects all negative literals; if the clause has none, its first literal; empty for `□`. */
  object AllNegativeSelector extends LiteralSelector:
    def select(bank: TermBank, literals: Array[Literal]): Array[Int] =
      if literals.isEmpty then EmptySelection
      else
        var count = 0
        var i = 0
        while i < literals.length do
          if bank.isNegative(literals(i)) then count += 1
          i += 1
        if count == 0 then Array(0)
        else
          val out: Array[Int] = new Array[Int](count)
          var n = 0
          i = 0
          while i < literals.length do
            if bank.isNegative(literals(i)) then
              out(n) = i
              n += 1
            i += 1
          out

  /**
   * The default selection: pick the single **best** literal under a deterministic, total quality
   * ordering, and select just that one. The ordering, in decreasing priority:
   *   1. a negative equality (`s ≠ t`) is preferred -- productive, removed by equality resolution;
   *   2. larger literal weight (more constraining ⇒ fewer, sharper inferences);
   *   3. negative over positive;
   *   4. a structural comparison of the atoms, purely a tie-break so the choice is total.
   * Equality is recognised via [[EqualitySymbol]] (the arity-2 symbol with code 0). This mirrors
   * Vampire's default selector (10) without its colour key, which is irrelevant here.
   */
  object BestLiteralSelector extends LiteralSelector:
    def select(bank: TermBank, literals: Array[Literal]): Array[Int] =
      if literals.isEmpty then EmptySelection
      else
        var best = 0
        var i = 1
        while i < literals.length do
          if compareQuality(bank, literals(i), literals(best)) > 0 then best = i
          i += 1
        Array(best)

    /** Positive result: `l1` is the better (more selectable) literal under the quality ordering. */
    private def compareQuality(bank: TermBank, l1: Literal, l2: Literal): Int =
      var c: Int = java.lang.Boolean.compare(isNegativeEquality(bank, l1), isNegativeEquality(bank, l2))
      if c != 0 then c
      else
        c = Integer.compare(bank.literalWeight(l1), bank.literalWeight(l2))
        if c != 0 then c
        else
          c = java.lang.Boolean.compare(bank.isNegative(l1), bank.isNegative(l2))
          if c != 0 then c
          else compareStructural(bank, bank.atomOf(l1), bank.atomOf(l2))

    /** Whether `l` is a negative equality literal `s ≠ t` (atom headed by [[EqualitySymbol]], arity 2). */
    private def isNegativeEquality(bank: TermBank, l: Literal): Boolean =
      if !bank.isNegative(l) then false
      else
        val a: Term = bank.atomOf(l)
        !bank.isVar(a) && bank.headSymbol(a) == EqualitySymbol && bank.arity(a) == 2

    /** A total, deterministic structural order on terms; used only to break ties. */
    private def compareStructural(bank: TermBank, s: Term, t: Term): Int =
      if s == t then 0 // hash-consed identity
      else
        val fs: Int = bank.functor(s)
        val ft: Int = bank.functor(t)
        if fs != ft then Integer.compare(fs, ft)
        else
          // equal functor implies the same symbol and arity; compare arguments left to right
          val n: Int = bank.arity(s)
          var i = 0
          var r = 0
          while i < n && r == 0 do
            r = compareStructural(bank, bank.arg(s, i), bank.arg(t, i))
            i += 1
          r

  private val EmptySelection: Array[Int] = Array.empty[Int]

  // -----------------------------------------------------------------------------------------
  // Clause
  // -----------------------------------------------------------------------------------------

  /**
   * How a [[Clause]] was derived, recorded for proof reconstruction. We store only the rule and the
   * parent clauses with the literal positions involved; the unifier is **not** stored -- it is
   * recomputed by re-unifying the recorded literals during reconstruction (as in E, Vampire and
   * Prover9). Parents are held by reference, so a clause transitively retains its whole derivation
   * DAG (see PossibleOptimizations.md for the memory note).
   */
  enum Justification:
    /** A clause from the input problem (no parents). */
    case Input
    /** Binary resolution of `left`'s literal `leftLit` against `right`'s `rightLit` (complementary). */
    case Resolution(left: Clause, leftLit: Int, right: Clause, rightLit: Int)
    /** Factoring of `parent`'s literals `lit1` and `lit2` (same polarity), unifying their atoms. */
    case Factoring(parent: Clause, lit1: Int, lit2: Int)

  /**
   * A clause is an array of [[Literal]]s (a disjunction); no canonical ordering or
   * deduplication is imposed at construction (see [[TermBank.mkClause]]). It caches its
   * weight and carries a unique id for later age-based selection, its [[Justification]] (how it was
   * derived) for proof reconstruction, its `age` (`max(parent ages) + 1`, `0` for input), and its
   * `selected` literal indices, computed by [[select]] when the clause is activated (so clauses
   * discarded before activation never pay for it). An empty literal array denotes the empty clause
   * (falsity).
   */
  final class Clause private[Core] (
      val literals: Array[Literal],
      val weight: Int,
      val id: Int,
      val justification: Justification,
      val age: Int):
    private var _selected: Array[Int] = null

    /**
     * The selected literal indices, set once by [[select]] when the clause is activated; `null`
     * before that (only active clauses are asked for their selection).
     */
    def selected: Array[Int] = _selected

    /**
     * Compute and store this clause's literal selection using `bank`'s [[LiteralSelector]], and
     * return it. Idempotent -- the selection is computed once and cached. Called when the clause
     * moves from the passive to the active set.
     */
    def select(bank: TermBank): Array[Int] =
      if _selected == null then _selected = bank.selector.select(bank, literals)
      _selected

    inline def size: Int = literals.length
    inline def isEmpty: Boolean = literals.length == 0
    override def toString: String = if isEmpty then "□" else literals.mkString("[", ", ", "]")

  // -----------------------------------------------------------------------------------------
  // Unification (Trail)
  // -----------------------------------------------------------------------------------------

  /**
   * Mutable unification state over a [[TermBank]]: a two-scope binding store plus a
   * backtrackable trail. A unification operand is a `(term, scope)` pair; the scope (`0` or
   * `1`) tags which clause a variable belongs to, so the same variable number occurring in
   * two clauses stays distinct without renaming (the LADR "context" idea, fixed to two
   * scopes). Bindings live in arrays indexed by `(scope, variable number)` -- the shared
   * arena terms are never mutated.
   *
   * `unify` records its bindings on the trail and never cleans up: a caller brackets a
   * unification attempt with `val s = save(); ...; restore(s)`, on both success and failure.
   * Between `unify` and `restore` the bindings form the MGU, consumed either by an [[Applier]]
   * (to instantiate the conclusion of an inference) or read directly for proof reconstruction.
   */
  final class Trail(val bank: TermBank):

    private inline val NScopes = 2
    private inline val GroundScope = 0 // ground terms have no variables, so their scope is irrelevant

    // boundTerm  : Scope -> Variable -> Term   -- the term bound to variable (scope, v), or `-1` if unbound
    // boundScope : Scope -> Variable -> Scope  -- that bound term's scope
    private val boundTerm: Array[Array[Term]] = Array.fill(NScopes)(Array.fill[Term](16)(-1))
    private val boundScope: Array[Array[Scope]] = Array.fill(NScopes)(new Array[Scope](16))

    // trail of bound (scope, variable) slots, replayed in reverse to undo bindings;
    // trailScope : Int -> Scope   and   trailVar : Int -> Variable   (both indexed by trail position)
    private var trailScope: Array[Scope] = new Array[Scope](64)
    private var trailVar: Array[Variable] = new Array[Variable](64)
    private var trailTop: Int = 0

    // reused operand worklist for `unify` (the top two entries form the current pair)
    private val stack: mutable.Stack[(Term, Scope)] = mutable.Stack.empty

    // reused per-scope memo for `occurs`: derefed terms already proven free of the searched variable.
    // Avoids re-walking shared subterms (the arena is a DAG); cleared at the start of each `occurs`.
    private val occursClean: Array[IntOpenHashSet] = Array.fill[IntOpenHashSet](NScopes)(new IntOpenHashSet())

    /** A checkpoint of the trail; pass it to [[restore]] to undo every binding made afterwards. */
    def save(): Int = trailTop

    /** Undo all bindings made since checkpoint `n`. */
    def restore(n: Int): Unit =
      while trailTop > n do
        trailTop -= 1
        boundTerm(trailScope(trailTop))(trailVar(trailTop)) = -1

    /**
     * Dereference `(t, s)`: follow variable bindings until reaching an unbound variable or a
     * non-variable. Ground results are normalised to [[GroundScope]] (their scope is
     * irrelevant), which lets identical ground terms short-circuit in [[unify]].
     */
    def deref(t: Term, s: Scope): (Term, Scope) =
      var ct: Term = t
      var cs: Scope = s
      var more = true
      while more do
        val h: Int = bank.functor(ct) // single header read; < 0 means a variable
        if h < 0 then
          val v: Variable = decodeVar(h)
          if v < boundTerm(cs).length && boundTerm(cs)(v) >= 0 then // v is bound
            ct = boundTerm(cs)(v)
            cs = boundScope(cs)(v)
          else more = false
        else more = false
      if bank.isGround(ct) then (ct, GroundScope) else (ct, cs)

    /**
     * Attempt to unify `(t1, s1)` with `(t2, s2)`, leaving the resulting bindings on the
     * trail. Returns `true` on success (the trail then holds the MGU) and `false` on failure
     * (any partial bindings remain on the trail). The caller restores the trail either way.
     * Scopes must be in `0 until NScopes`.
     */
    def unify(t1: Term, s1: Scope, t2: Term, s2: Scope): Boolean =
      stack.clear()
      stack.push((t1, s1))
      stack.push((t2, s2))
      while stack.nonEmpty do
        val (y, ys): (Term, Scope) = stack.pop()
        val (x, xs): (Term, Scope) = stack.pop()
        val (dx, dsx): (Term, Scope) = deref(x, xs)
        val (dy, dsy): (Term, Scope) = deref(y, ys)
        if dx != dy || dsx != dsy then
          val xVar: Boolean = bank.isVar(dx)
          val yVar: Boolean = bank.isVar(dy)
          if xVar && yVar then bind(bank.varNum(dx), dsx, dy, dsy)
          else if xVar then
            if occurs(dx, dsx, dy, dsy) then return false
            bind(bank.varNum(dx), dsx, dy, dsy)
          else if yVar then
            if occurs(dy, dsy, dx, dsx) then return false
            bind(bank.varNum(dy), dsy, dx, dsx)
          else if bank.headSymbol(dx) != bank.headSymbol(dy) then return false
          else
            val n: Int = bank.arity(dx)
            var i = 0
            while i < n do
              stack.push((bank.arg(dx, i), dsx))
              stack.push((bank.arg(dy, i), dsy))
              i += 1
      true

    /** Whether the unbound variable `(varT, varScope)` occurs in `(t, s)` (with dereferencing). */
    private def occurs(varT: Term, varScope: Scope, t: Term, s: Scope): Boolean =
      var sc = 0
      while sc < NScopes do
        occursClean(sc).clear()
        sc += 1
      occursRec(varT, varScope, t, s)

    private def occursRec(varT: Term, varScope: Scope, t: Term, s: Scope): Boolean =
      val (dt, ds): (Term, Scope) = deref(t, s)
      if bank.isVar(dt) then dt == varT && ds == varScope
      else if bank.isGround(dt) then false
      else if occursClean(ds).contains(dt) then false // already shown to not contain the variable
      else
        val n: Int = bank.arity(dt)
        var i = 0
        while i < n do
          if occursRec(varT, varScope, bank.arg(dt, i), ds) then return true
          i += 1
        occursClean(ds).add(dt) // mark this (term, scope) clean so shared occurrences are skipped
        false

    private def bind(v: Variable, s: Scope, t2: Term, s2: Scope): Unit =
      ensureVarCapacity(s, v)
      boundTerm(s)(v) = t2
      boundScope(s)(v) = s2
      if trailTop == trailScope.length then
        trailScope = java.util.Arrays.copyOf(trailScope, trailScope.length * 2)
        trailVar = java.util.Arrays.copyOf(trailVar, trailVar.length * 2)
      trailScope(trailTop) = s
      trailVar(trailTop) = v
      trailTop += 1

    private def ensureVarCapacity(s: Scope, v: Variable): Unit =
      val cur: Array[Int] = boundTerm(s)
      if v >= cur.length then
        var nl: Int = cur.length * 2
        while nl <= v do nl *= 2
        val nt: Array[Int] = java.util.Arrays.copyOf(cur, nl)
        java.util.Arrays.fill(nt, cur.length, nl, -1)
        boundTerm(s) = nt
        boundScope(s) = java.util.Arrays.copyOf(boundScope(s), nl)

    /** Capture the current bindings as an [[Applier]] for instantiating an inference's conclusion. */
    def applier(): Applier = new Applier

    /**
     * Instantiates `(term, scope)` operands into fresh shared terms under the trail's current
     * bindings. Each distinct unbound variable is consistently renamed to a fresh dense
     * variable (`0, 1, 2, ...`) across all calls on this instance, so the literals of one
     * conclusion share a coherent, normalised variable numbering.
     */
    final class Applier:
      private val outVars: mutable.HashMap[(Scope, Variable), Variable] = mutable.HashMap.empty
      // per-scope memo (derefed term -> instantiated term), so shared subterms are built once
      private val memo: Array[Int2IntOpenHashMap] = Array.fill[Int2IntOpenHashMap](NScopes) {
        val m: Int2IntOpenHashMap = new Int2IntOpenHashMap()
        m.defaultReturnValue(-1)
        m
      }

      def apply(t: Term, s: Scope): Term =
        val (dt, ds): (Term, Scope) = deref(t, s)
        if bank.isVar(dt) then bank.mkVar(outVars.getOrElseUpdate((ds, bank.varNum(dt)), outVars.size))
        else if bank.isGround(dt) then dt
        else
          val cached: Term = memo(ds).get(dt)
          if cached != -1 then cached
          else
            val n: Int = bank.arity(dt)
            val out: Array[Term] = new Array[Term](n)
            var i = 0
            while i < n do
              out(i) = apply(bank.arg(dt, i), ds)
              i += 1
            val res: Term = bank.mkApp(bank.headSymbol(dt), out)
            memo(ds).put(dt, res)
            res

  // -----------------------------------------------------------------------------------------
  // small helpers
  // -----------------------------------------------------------------------------------------

  private val EmptyArgs: Array[Int] = Array.empty[Int]

  /** Encode variable number `v` as a (negative) functor field. */
  private inline def encodeVar(v: Int): Int = -(v + 1)

  /** Decode a (negative) functor field back to a variable number. */
  private inline def decodeVar(fc: Int): Int = -fc - 1

  /** The free-variable-mask bit for variable number `v` (the overflow bit for `v >= 63`). */
  private inline def varBit(v: Int): Long = if v < 63 then 1L << v else FvOverflow
