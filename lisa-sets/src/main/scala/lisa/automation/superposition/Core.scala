package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.{Int2IntOpenCustomHashMap, Int2IntOpenHashMap, IntArrayList, IntHash, IntOpenHashSet}
import it.unimi.dsi.fastutil.longs.{LongArrays, LongComparator}

import scala.collection.mutable
import scala.util.hashing.MurmurHash3

/**
 * The core datastructures every other file in the package is built on: the symbol signature, a
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

  /** Zero-cost views between `Array[Term]` and `Array[Int]` (a `Term` *is* an `Int`). Defined here, where the
   *  opaque type is transparent, so external code can use the `Int`-array overloads (e.g. `java.util.Arrays.copyOf`)
   *  that do not resolve on the opaque `Array[Term]`. Inline ⇒ they compile to the identity (the same array). */
  inline def asArrayInt(array: Array[Term]): Array[Int] = array
  inline def asArrayTerm(array: Array[Int]): Array[Term] = array

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

  /** The arena offset backing a [[Term]]: a stable, unique `Int` key for hash-consed terms. Inline no-op. */
  extension (t: Term) inline def offset: Int = t

  /**
   * The equality predicate, reserved as the arity-2 symbol with code `0`: every [[Signature]]
   * pre-interns it at construction (under the name `"="`), so user symbols start at code 1 and no
   * other symbol can occupy code 0. Recognising it is needed for selection (preferring negative
   * equalities) and, later, for superposition.
   */
  val EqualitySymbol: Symbol = 0

  /** A unification scope (`0` or `1`): which of the two clauses a variable belongs to. A transparent alias, purely documentary. */
  type Scope = Int

  /** Default Knuth-Bendix weight given to a freshly interned symbol. */
  val defaultSymbolWeight: Int = 1

  /** KBO symbol-**weight** generation scheme (the weight twin of [[PrecedenceScheme]]).
   *  Applied at **intern time**, since term weights are cached when terms are built, so the scheme must be fixed
   *  on the [[Signature]] before any clause is constructed. */
  enum WeightScheme:
    /** All symbols weight [[defaultSymbolWeight]] (KBO `const`, Vampire's default and our historical one). */
    case Const
    /** `weight = arity + 1` (E's `arity` scheme): constants get `1 = VariableWeight` (admissible), so terms
     *  built from higher-arity symbols weigh more. */
    case Arity

  /**
   * The data for one interned symbol: immutable identity (`name`, `arity`, kind) and the
   * mutable ordering parameters used by KBO (`weight` and `precedence`). One instance is
   * allocated per distinct symbol. Terms refer to a symbol by its integer [[Symbol]] code
   * (`id`), so the hot paths index an array of these rather than dereferencing the object.
   *
   * `weight`/`precedence` are `def`-backed rather than plain `var`s so that **every** write bumps the
   * owning signature's [[Signature.orderingVersion]], the stamp any cache over the term ordering (today
   * [[Order]]'s orientation memo) checks to invalidate itself. Assignment syntax is unchanged.
   */
  /** @param name the identifier's bare name, and @param no its counter index, kept apart rather than as one
    *             `name_no` string so a consumer rebuilding a kernel identifier does not have to split the
    *             string back up (and get `Identifier("e_1", 0)` wrong where `Identifier("e", 1)` was meant). */
  final class SymbolInfo private[Core] (val id: Symbol, val name: String, val no: Int, val arity: Int, val isPredicate: Boolean, private val owner: Signature):
    private var _weight: Int = defaultSymbolWeight
    private var _precedence: Int = id

    /** Knuth-Bendix weight of this symbol. Read live by [[KBO]]; also folded into each term's cached weight
      * at construction, so a change after terms are built leaves those cached weights stale. */
    def weight: Int = _weight
    def weight_=(w: Int): Unit = { _weight = w; owner.bumpOrderingVersion() }

    /** Precedence rank of this symbol, read **live** by [[KBO]] (never cached into terms). */
    def precedence: Int = _precedence
    def precedence_=(p: Int): Unit = { _precedence = p; owner.bumpOrderingVersion() }

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
  final class Signature(weightScheme: WeightScheme = WeightScheme.Const):
    private val infos: mutable.ArrayBuffer[SymbolInfo] = mutable.ArrayBuffer.empty[SymbolInfo]
    // Keyed by the full symbol identity; see [[intern]]. Only touched during ingestion, never on a search
    // path, so a four-field key costs nothing that matters.
    private val index: mutable.HashMap[(String, Int, Int, Boolean), Symbol] = mutable.HashMap.empty
    private var _orderingVersion: Int = 0

    /**
     * A counter bumped by every write to any symbol's [[SymbolInfo.weight]] or [[SymbolInfo.precedence]].
     * i.e. by every change to the term ordering this signature induces (notably [[Precedence.assign]], which
     * runs *after* the clauses are built). Caches over the ordering compare it against the version they were
     * populated under and drop themselves when it moves, so no cache can outlive the parameters it was
     * computed from. See [[Order.orient]], the only such cache today.
     */
    def orderingVersion: Int = _orderingVersion
    private[Core] def bumpOrderingVersion(): Unit = _orderingVersion += 1

    // Reserve code 0 for the equality predicate (see [[EqualitySymbol]]); user symbols start at 1.
    intern("=", 2, isPredicate = true)

    /**
     * Intern a symbol, returning its (stable) code. The key is the whole quadruple (name, counter index,
     * arity and predicate-ness) because each of the four genuinely distinguishes source symbols:
     *
     *   - `no`, or `e` and `e_1` become one symbol;
     *   - `arity`, since a symbol's meaning depends on it;
     *   - `isPredicate`, which the key used to *accept and discard*. A name used at the same arity as both a
     *     predicate and a function then collapsed into a single symbol, with whichever occurrence interned
     *     first deciding the kind for both. TPTP input cannot express that (the positions are distinct), but
     *     a Lisa goal can: `Constant("p", Ind→Prop)` and `Constant("p", Ind→Ind)` are two legal kernel
     *     symbols. The prover could then resolve across them, which the kernel check catches on the tactic
     *     path and nothing catches on the CASC path.
     *
     * What it deliberately does *not* distinguish is a `Constant` from a `Variable` treated as a symbol (an
     * ε-abstraction symbol, say). Adding that alone would not close the class, since `Reconstruction` decides
     * which to rebuild by name membership in its schematic set; the generated namespaces keep them apart.
     *
     * Interning *after* [[Precedence.assign]] is sound but unprincipled: the new symbol keeps its default
     * precedence (its own code), which lands above every rank the scheme assigned, so it silently sits outside
     * the chosen [[PrecedenceScheme]]. The order stays total, so no completeness is lost.
     */
    def intern(name: String, no: Int, arity: Int, isPredicate: Boolean): Symbol =
      index.getOrElseUpdate(
        (name, no, arity, isPredicate), {
          val info: SymbolInfo = new SymbolInfo(infos.length, name, no, arity, isPredicate, this)
          info.weight = weightScheme match
            case WeightScheme.Const => defaultSymbolWeight
            case WeightScheme.Arity => arity + 1
          infos += info
          info.id
        }
      )

    /** Intern a symbol whose identifier carries no counter (`no = 0`): the built-in equality, and the
      * hand-built signatures in the tests. Kernel input goes through the four-argument form. */
    def intern(name: String, arity: Int, isPredicate: Boolean): Symbol = intern(name, 0, arity, isPredicate)

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

    /** The canonical KBO-based [[Order]] over this bank's terms, a **single** shared instance (one `orient`
     *  cache, one `KBO`) for the selector, the generating equality inferences, and demodulation. Lazy so it
     *  is built after the signature is in place; the KBO reads weights/precedence live, so early forcing is
     *  harmless. */
    lazy val order: Order = new Order(new KBO(this))

    // cached comparator (closing over this bank) for in-place primitive sorting of literal arrays
    private val literalOrder: LongComparator = (a, b) => compareLiterals(this, a, b)

    /** Sort `lits` in place into canonical literal order (see [[compareLiterals]]); no boxing. */
    def sortLiterals(lits: Array[Literal]): Unit = LongArrays.quickSort(lits, literalOrder)

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
    def mkClause(lits: Array[Literal], justification: Justification = Justification.Input, goalInput: Boolean = false): Clause =
      val id: Int = clauseCounter
      clauseCounter += 1
      buildClause(lits, justification, goalInput, id)

    /**
     * Build a clause that exists only to be handed to an index as a retrieval key -- forward/backward
     * subsumption ask "which stored clause is `≤`/`≥` this one?", and the trie and `Subsumption.subsumes`
     * both want a [[Clause]], not a bare literal array.
     *
     * It differs from [[mkClause]] in exactly one way: it does not draw an id from `clauseCounter`. Minting
     * one per literal per simplification call inflates the id space that real clauses live in, and ids are
     * used as identities and as hash keys (`ActiveSet.slot`, the lazy-deletion sets, the fingerprint entries),
     * so the spread is not free. Every query clause instead carries [[QueryClauseId]], which is negative and
     * shared: it can never collide with a real id, and it is deliberately useless as an identity, since a
     * query clause must never be stored (see [[Clause.isQuery]] and the guards in `ActiveSet`/`PassiveSet`).
     */
    def mkQueryClause(lits: Array[Literal]): Clause =
      buildClause(lits, Justification.Input, false, QueryClauseId)

    private def buildClause(lits: Array[Literal], justification: Justification, goalInput: Boolean, id: Int): Clause =
      var w = 0
      var pos = 0
      var predBits = 0L
      var i = 0
      while i < lits.length do
        val l: Literal = lits(i)
        w += literalWeight(l)
        if isPositive(l) then pos += 1
        predBits |= 1L << (headSymbol(atomOf(l)) & 63) // head-symbol fingerprint (mod 64)
        i += 1
      // One pass over the justification, packing `age` (high bits) and goal-ness (bit 0), so the two parallel
      // 8-case matches don't drift. Age: every generating rule is one generation past its premises; a
      // Canonicalization/Demodulation keeps the parent's age (same generation band). Goal-ness propagates as the
      // OR over premises (an input's is set by the caller), the boolean reduction of Vampire's `max` over the
      // input-type lattice.
      inline def pack(age: Int, goal: Boolean): Long = (age.toLong << 1) | (if goal then 1L else 0L)
      val packed: Long = justification match
        case Justification.Input                             => pack(0, goalInput)
        case Justification.Resolution(l, _, r, _)           => pack(math.max(l.age, r.age) + 1, l.isGoal || r.isGoal)
        case Justification.Factoring(p, _, _)               => pack(p.age + 1, p.isGoal)
        case Justification.Canonicalization(p)              => pack(p.age, p.isGoal)
        case Justification.Superposition(f, _, _, in, _, _) => pack(math.max(f.age, in.age) + 1, f.isGoal || in.isGoal)
        case Justification.EqualityResolution(p, _)         => pack(p.age + 1, p.isGoal)
        case Justification.EqualityFactoring(p, _, _, _, _) => pack(p.age + 1, p.isGoal)
        case Justification.Demodulation(t, _, _, ru, _)     => pack(math.max(t.age, ru.age), t.isGoal || ru.isGoal)
      new Clause(lits, w, id, justification, (packed >> 1).toInt, pos, lits.length - pos, predBits, (packed & 1L) != 0)

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
      h = MurmurHash3.mix(h, n)
      var i = 0
      while i < n do
        h = MurmurHash3.mix(h, mem(t + HeaderWords + i).toInt)
        i += 1
      MurmurHash3.finalizeHash(h, n + 2)

    /** Structural equality of two records by reading the arena (functor+arity, then children). */
    private def equalRecords(a: Term, b: Term): Boolean =
      val ha: Long = mem(a)
      if ha != mem(b) then false // packs functor + arity, so this compares both at once
      else
        val n: Int = (ha >>> 32).toInt
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
  // Syntactic orderings (a total, deterministic order on terms/literals; distinct from KBO)
  // -----------------------------------------------------------------------------------------

  /**
   * A total, deterministic structural order on terms: compare the raw functor (variables sort before
   * symbols, as their functor field is negative), then arguments left to right, bottoming out on
   * hash-consed identity. Used as a selection tie-break and as the canonical literal sort key; this
   * is purely syntactic and unrelated to the (semantic) [[KBO]].
   */
  def compareStructural(bank: TermBank, s: Term, t: Term): Int =
    if s == t then 0
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

  /**
   * Canonical order on literals: by atom ([[compareStructural]]), then by polarity (negative before
   * positive). This groups duplicate and complementary literals adjacently, so canonicalisation can
   * dedup and detect tautologies in a single pass over the sorted literals.
   */
  def compareLiterals(bank: TermBank, l1: Literal, l2: Literal): Int =
    val c: Int = compareStructural(bank, bank.atomOf(l1), bank.atomOf(l2))
    if c != 0 then c
    else java.lang.Boolean.compare(bank.isPositive(l1), bank.isPositive(l2))

  // Literal-selection strategies live in Selectors.scala (LiteralSelector and friends).

  // -----------------------------------------------------------------------------------------
  // Clause
  // -----------------------------------------------------------------------------------------

  /**
   * How a [[Clause]] was derived, recorded for proof reconstruction. We store only the rule and the
   * parent clauses with the literal positions involved; the unifier is **not** stored -- it is
   * recomputed by re-unifying the recorded literals during reconstruction (as in E, Vampire and
   * Prover9). Parents are held by reference, so a clause transitively retains its whole derivation
   * DAG (see `archive/PossibleOptimizations.md` for the memory note).
   */
  enum Justification:
    /** A clause from the input problem (no parents). */
    case Input
    /** Binary resolution of `left`'s literal `leftLit` against `right`'s `rightLit` (complementary). */
    case Resolution(left: Clause, leftLit: Int, right: Clause, rightLit: Int)
    /** Factoring of `parent`'s literals `lit1` and `lit2` (same polarity), unifying their atoms. */
    case Factoring(parent: Clause, lit1: Int, lit2: Int)

    /**
     * Sort + duplicate-removal canonicalisation of `parent`. The parent is retained only so the
     * derivation can be reconstructed and is **not** inserted into the clause sets. Sorting and
     * dropping identical literals are logical no-ops on a set of literals, so reconstruction treats
     * this as a pass-through for now -- but later simplifications recorded the same way will not be.
     */
    case Canonicalization(parent: Clause)

    /**
     * Superposition: rewrite `into`'s literal `intoLit` at subterm position `pos` (a path of argument
     * indices into the atom) using the positive equality at `from`'s literal `fromLit`, whose side
     * `fromSide` (0/1) is the rewriting LHS. Both parents are retained for reconstruction.
     */
    case Superposition(from: Clause, fromLit: Int, fromSide: Int, into: Clause, intoLit: Int, pos: Array[Int])
    /** Equality resolution: unify the two sides of `parent`'s negative equality `lit` (`s ≠ t`) and drop it. */
    case EqualityResolution(parent: Clause, lit: Int)
    /** Equality factoring on `parent`'s positive equalities: the maximal `dropped` is removed, `kept` retained;
     *  `droppedSide`/`keptSide` are the unified sides (`mgu` of `dropped`'s `droppedSide` and `kept`'s `keptSide`),
     *  recorded so reconstruction can recompute the substitution. */
    case EqualityFactoring(parent: Clause, dropped: Int, droppedSide: Int, kept: Int, keptSide: Int)

    /**
     * Demodulation (rewriting): `target`'s literal `targetLit` is rewritten at subterm position `pos`
     * (a path of argument indices into the atom) by the positive unit equality `rule`, whose side
     * `ruleSide` (0/1) is the matched left-hand side. A simplification; `target` is the rewritten premise.
     */
    case Demodulation(target: Clause, targetLit: Int, pos: Array[Int], rule: Clause, ruleSide: Int)

    /**
     * The clauses this inference was derived from, ignoring the literal positions and sides, i.e. the edges
     * out of this node of the derivation DAG. `Nil` for [[Input]].
     *
     * The one place the eight cases are enumerated for DAG *walking*, shared by every consumer that needs
     * only the edges (the proof cone, the derivation printer, tests counting input leaves), so a ninth rule is
     * one edit rather than a hunt. Deliberately **not** used by [[TermBank.mkClause]], which runs on every
     * clause ever built and would pay a `List` allocation for it; its own match also needs more than the
     * premises (whether the rule advances the age generation).
     */
    def premises: List[Clause] = this match
      case Input                                => Nil
      case Resolution(l, _, r, _)               => List(l, r)
      case Factoring(p, _, _)                   => List(p)
      case Canonicalization(p)                  => List(p)
      case Superposition(f, _, _, i, _, _)      => List(f, i)
      case EqualityResolution(p, _)             => List(p)
      case EqualityFactoring(p, _, _, _, _)     => List(p)
      case Demodulation(t, _, _, r, _)          => List(t, r)

  /** The [[Clause.id]] borne by every clause built with [[TermBank.mkQueryClause]]. Negative, so it cannot
    * collide with an id drawn from the clause counter, and shared by all query clauses, so any code that
    * treats it as an identity is wrong by construction rather than subtly. */
  final val QueryClauseId: Int = -1

  /**
   * A clause is an array of [[Literal]]s (a disjunction); no canonical ordering or
   * deduplication is imposed at construction (see [[TermBank.mkClause]]). It caches its
   * weight and carries a unique id for later age-based selection, its [[Justification]] (how it was
   * derived) for proof reconstruction, its `age` (`max(parent ages) + 1`, `0` for input), and its
   * `selected` literal indices, computed by [[select]] when the clause is activated (so clauses
   * discarded before activation never pay for it). An empty literal array denotes the empty clause
   * (falsity).
   *
   * It also caches a cheap **subsumption signature** -- `posCount`/`negCount` (literal polarity
   * counts) and `predBits` (a 64-bit fingerprint OR-ing one bit per literal's head-symbol code mod
   * 64). Together with `size` and `weight` these are what `Subsumption.sigSubsumes` compares for its
   * O(1) necessary-condition pre-filter on θ-subsumption; that method states the conditions and why
   * each one holds.
   */
  final class Clause private[Core] (
      val literals: Array[Literal],
      val weight: Int,
      val id: Int,
      val justification: Justification,
      val age: Int,
      val posCount: Int,
      val negCount: Int,
      val predBits: Long,
      /** Derived from the goal (negated conjecture): true for a goal input clause and for any clause with a goal
       *  parent. Used for goal-directed clause selection (Vampire's `nongoal_weight_coefficient`). */
      val isGoal: Boolean):
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

    private var _fromSides: List[(Int, Int, Term, Symbol)] = null
    private var _fromSidesVersion: Int = -1

    /**
     * This clause's usable superposition from-sides ([[Superposition.fromSides]] over its [[selected]]
     * literals), computed once and cached: the from-side analogue of [[select]], and activated clauses only,
     * since only they are ever asked.
     *
     * '''Why it is worth caching.''' The linear (non-indexed) generation scan asks every *active* clause for its
     * from-sides on every given, so the same list was rebuilt `|active| × |given|` times per saturation, one
     * tuple per usable side each time. Cached, it is built once per activated clause. The from-index maintenance
     * in [[ActiveSet]] reads it too, which makes its removal take out exactly the entries its insertion put in
     * rather than re-deriving equal ones.
     *
     * '''Why it is stamped.''' The sides depend on `Order.orient`, hence on the KBO's weights and precedence. A
     * verdict is only valid for the parameters it was computed under, so the cache carries the
     * [[Signature.orderingVersion]] it was built at and rebuilds when that moves, the same device
     * `Order`'s own orientation memo uses. Within one saturation the ordering is fixed and this never fires;
     * it is what keeps the cache honest if a clause outlives a re-assignment (a bank reused across two
     * saturations under different [[PrecedenceScheme]]s, as the A/B tests do).
     */
    def fromSides(bank: TermBank): List[(Int, Int, Term, Symbol)] =
      val version: Int = bank.signature.orderingVersion
      if _fromSides == null || _fromSidesVersion != version then
        _fromSides = Superposition.fromSides(bank, bank.order, this)
        _fromSidesVersion = version
      _fromSides

    inline def size: Int = literals.length
    inline def isEmpty: Boolean = literals.length == 0

    /** True for a clause built by [[TermBank.mkQueryClause]] as a throwaway index key. Its [[id]] is a shared
      * sentinel, so it must never be stored anywhere keyed by id -- the active and passive sets reject it. */
    inline def isQuery: Boolean = id == QueryClauseId

    override def toString: String = (if isQuery then "?" else "") + (if isEmpty then "□" else literals.mkString("[", ", ", "]"))

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

    // Count of currently-live bindings per scope (== number of trail entries carrying that scope). Kept in
    // sync by `bind`/`restore`, so `matchTerm` can assert its target scope is binding-free in O(1).
    private val liveBindings: Array[Int] = Array.fill(NScopes)(0)

    // reused worklist for `unify`: two parallel primitive int stacks (no boxing, no tuple allocation)
    private val workTerm: IntArrayList = new IntArrayList()
    private val workScope: IntArrayList = new IntArrayList()

    // reused worklist for `matchTerm`: pattern terms paired with target terms (scopes are fixed args)
    private val matchPat: IntArrayList = new IntArrayList()
    private val matchTgt: IntArrayList = new IntArrayList()

    // reused per-scope memo for `occurs`: derefed terms already proven free of the searched variable.
    // Avoids re-walking shared subterms (the arena is a DAG); cleared at the start of each `occurs`.
    private val occursClean: Array[IntOpenHashSet] = Array.fill[IntOpenHashSet](NScopes)(new IntOpenHashSet())

    /** A checkpoint of the trail; pass it to [[restore]] to undo every binding made afterwards. */
    def save(): Int = trailTop

    /** Undo all bindings made since checkpoint `n`. */
    def restore(n: Int): Unit =
      while trailTop > n do
        trailTop -= 1
        liveBindings(trailScope(trailTop)) -= 1
        boundTerm(trailScope(trailTop))(trailVar(trailTop)) = -1

    /**
     * Dereference `(t, s)`: follow variable bindings until reaching an unbound variable or a
     * non-variable. The result `(term, scope)` is packed into a single `Long` (term in the high 32
     * bits, scope in the low 32) to avoid allocating a tuple on this hot path; unpack with
     * [[derefTerm]]/[[derefScope]]. Ground results are normalised to [[GroundScope]] (their scope is
     * irrelevant), which lets identical ground terms short-circuit in [[unify]].
     */
    private def deref(t: Term, s: Scope): Long =
      var ct: Term = t
      var cs: Scope = s
      var more = true
      while more do
        val h: Int = bank.functor(ct) // single header read; < 0 means a variable
        if h < 0 then
          val v: Variable = decodeVar(h)
          val bt: Array[Term] = boundTerm(cs) // stable within this deref (no bind happens here)
          if v < bt.length && bt(v) >= 0 then
            ct = bt(v)
            cs = boundScope(cs)(v)
          else more = false
        else more = false
      val rs: Scope = if bank.isGround(ct) then GroundScope else cs
      (ct.toLong << 32) | (rs.toLong & 0xFFFFFFFFL)

    /** The term packed by [[deref]] (high 32 bits). */
    private inline def derefTerm(packed: Long): Term = (packed >>> 32).toInt

    /** The scope packed by [[deref]] (low 32 bits). */
    private inline def derefScope(packed: Long): Scope = packed.toInt

    /**
     * Attempt to unify `(t1, s1)` with `(t2, s2)`, leaving the resulting bindings on the
     * trail. Returns `true` on success (the trail then holds the MGU) and `false` on failure
     * (any partial bindings remain on the trail). The caller restores the trail either way.
     * Scopes must be in `0 until NScopes`.
     */
    def unify(t1: Term, s1: Scope, t2: Term, s2: Scope): Boolean =
      workTerm.clear()
      workScope.clear()
      workTerm.push(t1); workScope.push(s1)
      workTerm.push(t2); workScope.push(s2)
      while !workTerm.isEmpty do
        val y: Term = workTerm.popInt(); val ys: Scope = workScope.popInt()
        val x: Term = workTerm.popInt(); val xs: Scope = workScope.popInt()
        val px: Long = deref(x, xs); val dx: Term = derefTerm(px); val dsx: Scope = derefScope(px)
        val py: Long = deref(y, ys); val dy: Term = derefTerm(py); val dsy: Scope = derefScope(py)
        if dx != dy || dsx != dsy then
          if bank.isVar(dx) then
            if bank.isVar(dy) then bind(bank.varNum(dx), dsx, dy, dsy) // both variables
            else
              if occurs(dx, dsx, dy, dsy) then return false
              bind(bank.varNum(dx), dsx, dy, dsy)
          else if bank.isVar(dy) then
            if occurs(dy, dsy, dx, dsx) then return false
            bind(bank.varNum(dy), dsy, dx, dsx)
          else if bank.headSymbol(dx) != bank.headSymbol(dy) then return false
          else
            val n: Int = bank.arity(dx)
            var i = 0
            while i < n do
              workTerm.push(bank.arg(dx, i)); workScope.push(dsx)
              workTerm.push(bank.arg(dy, i)); workScope.push(dsy)
              i += 1
      true

    /**
     * One-sided (first-order) matching: extend the current bindings so that `(pat, ps)` becomes
     * syntactically equal to `(tgt, ts)`, binding **only** pattern-scope (`ps`) variables and treating
     * the target as rigid. Returns `true` on success -- the trail then holds the matcher, an extension
     * of any incoming bindings -- and `false` on failure, leaving partial bindings on the trail; the
     * caller restores the trail either way, exactly the [[unify]] protocol. The two scopes must
     * differ (`ps != ts`, the usual `0`/`1`), and the **target scope `ts` must carry no live bindings**:
     * target terms are treated as rigid (a bound target variable is never dereferenced), so a live `ts`
     * binding would be silently mis-matched, breaking subsumption soundness. Both preconditions are
     * asserted at entry (the `ts`-clean check is O(1) via [[liveBindings]]).
     *
     * Cheaper than unification: target variables never bind, so there are no chains to follow and **no occurs
     * check**. A re-encountered bound pattern variable is re-checked by a single offset comparison (`bound != t`),
     * since structurally equal targets are hash-consed to one offset and every binding lives in scope `ts`.
     */
    def matchTerm(pat: Term, ps: Scope, tgt: Term, ts: Scope): Boolean =
      assert(ps != ts, "matchTerm: pattern and target scopes must differ")
      assert(liveBindings(ts) == 0, "matchTerm: target scope must have no live bindings (target terms are treated as rigid)")
      matchPat.clear()
      matchTgt.clear()
      matchPat.push(pat); matchTgt.push(tgt)
      while !matchPat.isEmpty do
        val p: Term = matchPat.popInt()
        val t: Term = matchTgt.popInt()
        if bank.isVar(p) then
          val v: Variable = bank.varNum(p)
          val bt: Array[Term] = boundTerm(ps)
          val bound: Term = if v < bt.length then bt(v) else -1
          if bound < 0 then bind(v, ps, t, ts) // unbound pattern variable: bind it to the target term
          else if bound != t then return false // bound already: the target must be the identical term
        else if bank.isVar(t) then return false // pattern compound vs a rigid target variable
        else if bank.headSymbol(p) != bank.headSymbol(t) then return false
        else
          val n: Int = bank.arity(p) // equal head symbols imply equal arity
          var i = 0
          while i < n do
            matchPat.push(bank.arg(p, i)); matchTgt.push(bank.arg(t, i))
            i += 1
      true

    /** Match literal `pl` (pattern, scope `ps`) onto `tl` (target, scope `ts`): same polarity and the
     *  atoms match one-sidedly. Extends the trail like [[matchTerm]]; the caller restores it. */
    def matchLiteral(pl: Literal, ps: Scope, tl: Literal, ts: Scope): Boolean =
      bank.isPositive(pl) == bank.isPositive(tl) && matchTerm(bank.atomOf(pl), ps, bank.atomOf(tl), ts)

    /** Whether the unbound variable `(varT, varScope)` occurs in `(t, s)` (with dereferencing). */
    private def occurs(varT: Term, varScope: Scope, t: Term, s: Scope): Boolean =
      var sc = 0
      while sc < NScopes do
        occursClean(sc).clear()
        sc += 1
      occursRec(varT, varScope, t, s)

    private def occursRec(varT: Term, varScope: Scope, t: Term, s: Scope): Boolean =
      val p: Long = deref(t, s); val dt: Term = derefTerm(p); val ds: Scope = derefScope(p)
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
      liveBindings(s) += 1

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
        val p: Long = deref(t, s); val dt: Term = derefTerm(p); val ds: Scope = derefScope(p)
        if bank.isVar(dt) then bank.mkVar(outVars.getOrElseUpdate((ds, bank.varNum(dt)), outVars.size))
        else if bank.isGround(dt) then dt
        else
          val m: Int2IntOpenHashMap = memo(ds)
          val cached: Term = m.get(dt)
          if cached != -1 then cached
          else
            val n: Int = bank.arity(dt)
            val out: Array[Term] = new Array[Term](n)
            var i = 0
            while i < n do
              out(i) = apply(bank.arg(dt, i), ds)
              i += 1
            val res: Term = bank.mkApp(bank.headSymbol(dt), out)
            m.put(dt, res)
            res

      /** Instantiate a whole literal in scope `s` under the current bindings, preserving its polarity. */
      def applyLit(l: Literal, s: Scope): Literal =
        bank.mkLiteral(apply(bank.atomOf(l), s), bank.isPositive(l))

      /** Copy every literal of `lits` except index `skip`, each instantiated in scope `s`, into `out` starting
       *  at index `from`; returns the next free index. The shared surviving-literal copy used by the generating
       *  builds ([[Inference.resolve]]/`factor`, [[Superposition.superpose]] and the equality inferences). */
      def copyLitsExcept(lits: Array[Literal], skip: Int, s: Scope, out: Array[Literal], from: Int): Int =
        var n = from
        var k = 0
        while k < lits.length do { if k != skip then { out(n) = applyLit(lits(k), s); n += 1 }; k += 1 }
        n

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
