package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.{Int2IntOpenCustomHashMap, Int2IntOpenHashMap, IntArrayList, IntHash, IntOpenHashSet}
import it.unimi.dsi.fastutil.longs.{LongArrays, LongComparator}

import scala.collection.mutable
import scala.util.hashing.MurmurHash3
import lisa.automation.superposition.ordering.*

/** The syntax used by the prover. A hash-consed term bank over one
  * flat array, packed literals, clauses, and unification. The README describes the encoding these
  * declarations assume. */
object Core:

  /** A reference to a term: the offset of its record in a [[TermBank]]'s arena. */
  opaque type Term = Int

  /** Views between `Array[Term]` and `Array[Int]`, so that callers can reach the `Int` overloads of library
   *  methods such as `java.util.Arrays.copyOf`. Inline, so both compile to the identity. */
  inline def asArrayInt(array: Array[Term]): Array[Int] = array
  inline def asArrayTerm(array: Array[Int]): Array[Term] = array

  /** A literal: an atom [[Term]] together with a polarity, packed as `(atom << 1) | sign`. */
  opaque type Literal = Long

  /** A symbol code as handed out by a [[Signature]] (always `>= 0`); this is what a term stores as its head. */
  opaque type Symbol = Int

  /** A variable's number (`>= 0`); distinct from a [[Symbol]] at the type level, though both are `Int` at runtime. */
  opaque type Variable = Int

  inline def Variable(num: Int): Variable = num

  extension (v: Variable) inline def num: Int = v
  extension (f: Symbol) inline def code: Int = f

  /** The arena offset backing a [[Term]]: a stable, unique `Int` key for hash-consed terms. Inline no-op. */
  extension (t: Term) inline def offset: Int = t

  /** The equality predicate, pre-interned by every [[Signature]] as the arity-2 symbol with code `0`. */
  val EqualitySymbol: Symbol = 0

  /** A unification scope (`0` or `1`), telling which of the two clauses a variable belongs to. */
  type Scope = Int

  /** Default Knuth-Bendix weight given to a freshly interned symbol. */
  val defaultSymbolWeight: Int = 1

  /** How KBO symbol weights are assigned, as a function of arity. Applied when a symbol is interned, since term
   *  weights are cached at construction, so the scheme must be fixed before any clause is built. */
  enum WeightScheme:
    /** Every symbol weighs [[defaultSymbolWeight]]. Vampire's default. */
    case Const
    /** `weight = arity + 1`, so terms over higher-arity symbols weigh more. E's `arity` scheme. */
    case Arity

    /** The weight this scheme gives a symbol of arity `arity`. Each case's meaning lives here rather than
      * being unfolded where symbols are interned, so a new scheme is a new case and nothing else. */
    def weightOf(arity: Int): Int = this match
      case Const => defaultSymbolWeight
      case Arity => arity + 1

  /**
   * One interned symbol: its identity, and the weight and precedence that KBO reads.
   *
   * @param name the identifier's bare name and @param no its counter index, stored apart rather than as one
   *             `name_no` string, so that rebuilding a kernel identifier does not have to split it back up
   *             and produce `Identifier("e_1", 0)` where `Identifier("e", 1)` was meant.
   */
  final class SymbolInfo private[Core] (val id: Symbol, val name: String, val no: Int, val arity: Int, val isPredicate: Boolean,
                                        /** Fixed at interning by the signature's weight function, and immutable
                                          * because each term folds it into a cached total weight at
                                          * construction: a later change would leave every existing term stale. */
                                        val weight: Int):
    /** Read live by [[KBO]] and never cached into terms, unlike [[weight]]. Defaults to the interning order and
      * is written once per run, by [[Precedence.assign]], which cannot compute it earlier: the default scheme
      * ranks symbols by how often they occur across all the input clauses, so it needs every clause first. */
    var precedence: Int = id

    override def toString: String = s"$name/$arity"

  // --- Signature ------------------------------------------------------------------------------------------

  /** Interns symbols into dense non-negative codes and holds their KBO parameters. Precedence defaults to the
   *  interning order and is normally reassigned by [[Precedence.assign]] once the whole signature is known. */
  final class Signature(weightOf: Int => Int = WeightScheme.Const.weightOf):
    private val infos: mutable.ArrayBuffer[SymbolInfo] = mutable.ArrayBuffer.empty[SymbolInfo]
    /** The full record for symbol `f`; access its fields directly, storing it in a val when several are needed. */
    def info(f: Symbol): SymbolInfo = infos(f)
    
    // Keyed by the full symbol identity; see [[intern]]. Only touched during ingestion, never on a search
    // path, so a four-field key costs nothing that matters.
    private val index: mutable.HashMap[(String, Int, Int, Boolean), Symbol] = mutable.HashMap.empty

    // Reserve code 0 for the equality predicate (see [[EqualitySymbol]]); user symbols start at 1.
    intern("=", 2, isPredicate = true)

    /** Intern a symbol, returning its stable code. All four components of the key distinguish source symbols:
      * dropping `no` merges `e` with `e_1`, and dropping `isPredicate` merges a predicate with a function of
      * the same name and arity, which a Lisa goal can declare and across which the prover would then resolve.
      *
      * Interning after [[Precedence.assign]] is sound but leaves the new symbol with its default precedence,
      * outside the assigned scheme. The order stays total, so completeness is unaffected. */
    def intern(name: String, no: Int, arity: Int, isPredicate: Boolean): Symbol =
      index.getOrElseUpdate(
        (name, no, arity, isPredicate), {
          val info: SymbolInfo = new SymbolInfo(infos.length, name, no, arity, isPredicate, weightOf(arity))
          infos += info
          info.id
        }
      )

    /** Intern a symbol whose identifier carries no counter (`no = 0`): the built-in equality, and the
      * hand-built signatures in the tests. Kernel input goes through the four-argument form. */
    def intern(name: String, arity: Int, isPredicate: Boolean): Symbol = intern(name, 0, arity, isPredicate)

    def size: Int = infos.length


    /** Compare two symbols by precedence: negative if `f < g`, positive if `f > g`, `0` if equal. */
    def comparePrecedence(f: Symbol, g: Symbol): Int = Integer.compare(infos(f).precedence, infos(g).precedence)
    def comparePrecedence(f: SymbolInfo, g: SymbolInfo): Int = Integer.compare(f.precedence, g.precedence)

    /** All interned symbols, in code order (read-only; for admissibility checks and diagnostics). */
    def symbols: Iterator[SymbolInfo] = infos.iterator

  // --- Term bank (flat arena + offset-keyed hash-consing) -------------------------------------------------

  /** Variable weight used by KBO; cached into each term's total weight at construction. */
  inline val VariableWeight = 1

  /** Overflow bit of a free-variable mask: set when some variable numbered `>= 63` occurs. */
  val FvOverflow: Long = 1L << 63

  /**
   * A hash-consed store of terms in one growable `Array[Long]`, in which a [[Term]] is the offset of its
   * record. Record layout at offset `p`, with `n` the arity:
   * {{{
   *   mem(p + 0) = (functor & 0xFFFFFFFFL) | (n.toLong << 32)   // functor (<0 = var) + arity
   *   mem(p + 1) = free-variable mask
   *   mem(p + 2) = total KBO weight (low 32 bits)
   *   mem(p + 3 .. p + 2 + n) = the n child offsets
   * }}}
   *
   * Hash-consing is write-first: the candidate record is appended at the bump pointer so it can be hashed and
   * compared by offset like any stored entry, and the pointer is rewound on a hit. No key object is built.
   */
  final class TermBank(val signature: Signature):

    private inline val HeaderWords = 3

    // --- arena --------------------------------------------------------------------------------------------
    private var mem: Array[Long] = new Array[Long](1024)
    private var end: Int = 0 // bump pointer: next free arena slot

    // --- hash-consing: fastutil map keyed on term content via a custom strategy ---------------------------
    private val hashConsStrategy: IntHash.Strategy = new IntHash.Strategy {
      def hashCode(t: Int): Int = hashOf(t)
      def equals(a: Int, b: Int): Boolean = equalRecords(a, b)
    }

    // maps a term offset to the canonical offset of its (content-)equal term
    // hashConsStrategy compares for equality of the record in the term bank, not equality of the offset ("term") itself.
    // In particular, it always hold that hashConsStrategy.equals(t, hashCons.get(t)) but not t == hashCons.get(t).
    // `hashCons` is really a map from `term record` to `term offset`, except that the record is given through an offset.
    private val hashCons: Int2IntOpenCustomHashMap =
      val m: Int2IntOpenCustomHashMap = new Int2IntOpenCustomHashMap(hashConsStrategy)
      m.defaultReturnValue(-1)
      m

    private var clauseCounter: Int = 0

    private var _selector: LiteralSelector = null

    /** The literal-selection strategy applied by [[Clause.select]] at activation; assign to plug in another.
      * Defaults to the refutation-complete [[CompleteBestLiteralSelector]], which is what
      * [[SearchOptions.selection]] ships, so a bank used directly selects as the prover does. Resolved on first
      * read, so a bank whose clauses are never activated builds no [[Order]]. */
    def selector: LiteralSelector =
      if _selector == null then _selector = new CompleteBestLiteralSelector(order)
      _selector

    def selector_=(s: LiteralSelector): Unit = _selector = s

    /** The one [[Order]] over this bank's terms, shared by the selector, the equality inferences and
      * demodulation, so that they share its orientation cache. */
    lazy val order: Order = new Order(new KBO(this))

    // cached comparator (closing over this bank) for in-place primitive sorting of literal arrays
    private val literalOrder: LongComparator = (a, b) => compareLiterals(this, a, b)

    /** Sort `lits` in place into canonical literal order (see [[compareLiterals]]); no boxing. */
    def sortLiterals(lits: Array[Literal]): Unit = LongArrays.quickSort(lits, literalOrder)

    // --- constructors -------------------------------------------------------------------------------------

    /** The shared term for variable number `v` (`v >= 0`). */
    def mkVar(v: Variable): Term =
      require(v >= 0, s"variable number must be non-negative, got $v")
      ensureMem(HeaderWords)
      val p: Int = end
      mem(p) = encodeVar(v).toLong & 0xFFFFFFFFL // arity 0, so high word is 0
      mem(p + 1) = varBit(v)
      mem(p + 2) = VariableWeight.toLong
      end = p + HeaderWords
      hashConsCandidate(p)

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
      hashConsCandidate(p)

    // --- accessors ----------------------------------------------------------------------------------------

    /** Raw functor field: `< 0` for variables, the symbol code otherwise. */
    inline def functor(t: Term): Int = mem(t).toInt // low 32 bits, sign-extended

    inline def isVar(t: Term): Boolean = functor(t) < 0

    /** Variable number of a variable term (undefined for non-variables). */
    inline def varNum(t: Term): Variable = decodeVar(functor(t))

    /** Head symbol of a compound/constant term (undefined for variables). */
    inline def headSymbol(t: Term): Symbol = functor(t)

    /** Number of arguments (`0` for variables and constants). */
    inline def arity(t: Term): Int = (mem(t) >>> 32).toInt

    inline def arg(t: Term, i: Int): Term = mem(t + HeaderWords + i).toInt

    /** Cached total KBO weight of `t`. */
    inline def weight(t: Term): Int = mem(t + 2).toInt

    /** Cached free-variable mask of `t` (see the object docs for the encoding). */
    inline def freeVarMask(t: Term): Long = mem(t + 1)

    /** A term is ground iff it has no free variables. */
    inline def isGround(t: Term): Boolean = freeVarMask(t) == 0L

    /** Whether `t` is an equality atom `s = t`, and the whole test: a variable's functor is negative so it
      * cannot match [[EqualitySymbol]] (`0`), and `=` is interned with arity 2, which [[mkApp]] enforces, so
      * neither an `isVar` nor an arity guard adds anything. */
    inline def isEqualityAtom(t: Term): Boolean = functor(t) == EqualitySymbol

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

    // --- literals -----------------------------------------------------------------------------------------

    def mkLiteral(atom: Term, positive: Boolean): Literal = (atom.toLong << 1) | (if positive then 1L else 0L)

    def atomOf(l: Literal): Term = (l >>> 1).toInt

    def isPositive(l: Literal): Boolean = (l & 1L) == 1L
    def isNegative(l: Literal): Boolean = (l & 1L) == 0L

    def negate(l: Literal): Literal = l ^ 1L

    /** Cached weight of a literal (its atom's weight). */
    def literalWeight(l: Literal): Int = weight(atomOf(l))

    /** Whether `l`'s atom is an equality `s = t` (see [[isEqualityAtom]]). */
    inline def isEquality(l: Literal): Boolean = isEqualityAtom(atomOf(l))

    /** Whether `l` is a negative equality `s ≠ t`, the literal shape equality resolution can remove. */
    inline def isNegativeEquality(l: Literal): Boolean = isNegative(l) && isEquality(l)

    // --- clauses ------------------------------------------------------------------------------------------

    /** Build a clause from `lits`, taking ownership of the array. It does not deduplicate, sort or drop
     *  tautologies; that is [[Inference.canonicalize]]'s job. An empty array is the empty clause. */
    def mkClause(lits: Array[Literal], justification: Justification = Justification.Input, goalInput: Boolean = false): Clause =
      val id: Int = clauseCounter
      clauseCounter += 1
      buildClause(lits, justification, goalInput, id)

    /** Build a [[QueryClause]], the throwaway an index retrieval is keyed on; see that class. */
    def mkQueryClause(lits: Array[Literal]): QueryClause =
      withSignature(lits)((w, pos, bits) => new QueryClause(lits, w, pos, lits.length - pos, bits))

    /** Compute a literal array's cached signature -- total weight, positive count, and the head-symbol mask --
      * in one pass, and hand the three to `use`. `inline`, so the function literal is beta-reduced away and both
      * builders share the loop without paying a closure or a second traversal for it. */
    private inline def withSignature[A](lits: Array[Literal])(inline use: (Int, Int, Long) => A): A =
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
      use(w, pos, predBits)

    private def buildClause(lits: Array[Literal], justification: Justification, goalInput: Boolean, id: Int): Clause =
      withSignature(lits) { (w, pos, predBits) =>
      // Age and goal-ness in one match, so they cannot drift apart: a generating rule is one generation past
      // its premises, canonicalization and demodulation stay in it, and goal-ness is their disjunction.
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
      }

    // --- internals ----------------------------------------------------------------------------------------

    /** Look up the record just written at offset `p`. On a hit, rewind the bump pointer and return the stored
      * term; on a miss, keep `p`. `putIfAbsent` does both in one probe, returning `-1` when absent. */
    private def hashConsCandidate(p: Term): Term =
      val existing: Term = hashCons.putIfAbsent(p, p)
      if existing != -1 then
        end = p // rewind: discard the candidate we just wrote
        existing
      else p

    /** Hash a term over functor, arity and children. Uses the incremental `MurmurHash3` API, which is the same
     *  protocol as `productHash` but folds the words straight out of the arena with no intermediate array. */
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

  // --- Syntactic orderings (a total, deterministic order on terms/literals; distinct from KBO) ------------

  /** A total, deterministic structural order on terms: the raw functor first (variables sort before symbols,
    * their functor being negative), then arguments left to right, bottoming out on hash-consed identity. A
    * selection tie-break and the canonical literal sort key; purely syntactic, unrelated to the [[KBO]]. */
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

  /** Canonical order on literals: by atom ([[compareStructural]]), then by polarity (negative before
    * positive). This groups duplicate and complementary literals adjacently, so canonicalisation can
    * dedup and detect tautologies in a single pass over the sorted literals. */
  def compareLiterals(bank: TermBank, l1: Literal, l2: Literal): Int =
    val c: Int = compareStructural(bank, bank.atomOf(l1), bank.atomOf(l2))
    if c != 0 then c
    else java.lang.Boolean.compare(bank.isPositive(l1), bank.isPositive(l2))

  // Literal-selection strategies live in Selectors.scala (LiteralSelector and friends).

  // --- Clause ---------------------------------------------------------------------------------------------

  /** How a [[Clause]] was derived, recorded for proof reconstruction: the rule, the parent clauses and the
    * literal positions involved. The unifier is not stored but recomputed during reconstruction, as in E,
    * Vampire and Prover9. Parents are held by reference, so a clause keeps its whole derivation alive. */
  enum Justification:
    /** A clause from the input problem (no parents). */
    case Input
    /** Binary resolution of `left`'s literal `leftLit` against `right`'s `rightLit` (complementary). */
    case Resolution(left: Clause, leftLit: Int, right: Clause, rightLit: Int)
    /** Factoring of `parent`'s literals `lit1` and `lit2` (same polarity), unifying their atoms. */
    case Factoring(parent: Clause, lit1: Int, lit2: Int)

    /** Sorting and duplicate removal on `parent`. Both are no-ops on a set of literals, so reconstruction
     *  treats this as a pass-through. */
    case Canonicalization(parent: Clause)

    /** Superposition: rewrite `into`'s literal `intoLit` at subterm position `pos`, a path of argument indices
     *  into the atom, using the equality at `from`'s literal `fromLit` with side `fromSide` as the left side. */
    case Superposition(from: Clause, fromLit: Int, fromSide: Int, into: Clause, intoLit: Int, pos: Array[Int])
    /** Equality resolution: unify the two sides of `parent`'s negative equality `lit` (`s ≠ t`) and drop it. */
    case EqualityResolution(parent: Clause, lit: Int)
    /** Equality factoring on `parent`'s positive equalities: the maximal `dropped` is removed, `kept` retained;
     *  `droppedSide`/`keptSide` are the unified sides (`mgu` of `dropped`'s `droppedSide` and `kept`'s `keptSide`),
     *  recorded so reconstruction can recompute the substitution. */
    case EqualityFactoring(parent: Clause, dropped: Int, droppedSide: Int, kept: Int, keptSide: Int)

    /** Demodulation: `target`'s literal `targetLit` is rewritten at position `pos` by the positive unit
     *  equality `rule`, whose side `ruleSide` matched. */
    case Demodulation(target: Clause, targetLit: Int, pos: Array[Int], rule: Clause, ruleSide: Int)

    /** The parent clauses: the edges out of this node of the derivation graph, and the one place the cases are
      * enumerated for walking. Not used by [[TermBank.mkClause]], which would pay its `List` per clause built. */
    def premises: List[Clause] = this match
      case Input                                => Nil
      case Resolution(l, _, r, _)               => List(l, r)
      case Factoring(p, _, _)                   => List(p)
      case Canonicalization(p)                  => List(p)
      case Superposition(f, _, _, i, _, _)      => List(f, i)
      case EqualityResolution(p, _)             => List(p)
      case EqualityFactoring(p, _, _, _, _)     => List(p)
      case Demodulation(t, _, _, r, _)          => List(t, r)

  /**
   * A disjunction of [[Literal]]s, with no ordering or deduplication imposed at construction, together with the
   * quantities cached from them: the total `weight`, the polarity counts, and `predBits`, a mask with one bit
   * per literal head symbol modulo 64. Those four are the subsumption signature `Subsumption.sigSubsumes`
   * compares; that method states what each is for. An empty literal array is the empty clause.
   *
   * This is everything a *subsumption question* needs, and it is a base class rather than a trait so that
   * reading these through it stays a field load: `sigSubsumes` reads five of them per candidate pair, which is
   * the most-executed predicate in the prover.
   *
   * The two subclasses are the answer to "does this clause have an identity": a [[Clause]] is a real derived
   * clause with an id, a derivation and a place in the search; a [[QueryClause]] is a throwaway built only to
   * ask an index a question. Anything that stores clauses asks for a `Clause`, so a query cannot reach it.
   */
  sealed abstract class ClauseBody private[Core] (
      val literals: Array[Literal],
      val weight: Int,
      val posCount: Int,
      val negCount: Int,
      val predBits: Long):
    inline def size: Int = literals.length
    inline def isEmpty: Boolean = literals.length == 0

  /**
   * A throwaway clause used only as an index retrieval key: the literal combination whose subsumers or
   * subsumees `Simplifier` is asking about. It has no id, no derivation and no selection, because it is never
   * stored, never simplified and never appears in a proof -- it exists for the duration of one index query.
   */
  final class QueryClause private[Core] (lits: Array[Literal], weight: Int, posCount: Int, negCount: Int, predBits: Long)
      extends ClauseBody(lits, weight, posCount, negCount, predBits):
    override def toString: String = literals.mkString("?[", ", ", "]")

  /** A clause the prover derived and may store: it carries an identity, the [[Justification]] that produced it,
    * and the caches that identity makes worthwhile. */
  final class Clause private[Core] (
      lits: Array[Literal],
      w: Int,
      val id: Int,
      val justification: Justification,
      val age: Int,
      pos: Int,
      neg: Int,
      bits: Long,
      /** Derived from the goal (negated conjecture): true for a goal input clause and for any clause with a goal
       *  parent. Used for goal-directed clause selection (Vampire's `nongoal_weight_coefficient`). */
      val isGoal: Boolean)
      extends ClauseBody(lits, w, pos, neg, bits):
    private var _selected: Array[Int] = null

    /** The selected literal indices, set once by [[select]] at activation; `null` before that. */
    def selected: Array[Int] = _selected

    /** The literal selection, computed once by `bank`'s [[LiteralSelector]] and cached. Called when the
      * clause is activated, so a clause discarded before that never pays for it. */
    def select(bank: TermBank): Array[Int] =
      if _selected == null then _selected = bank.selector.select(bank, literals)
      _selected

    private var _rewriteSources: Array[RewriteSource] = null

    /** The rewrites this clause offers superposition ([[Superposition.rewriteSources]]), cached: `ActiveSet`
      * reads them on both insertion and removal, so caching is what makes removal take out what insertion put
      * in. Which sides qualify depends on the term ordering, which is fixed for the run by the time any clause
      * is activated -- see [[Precedence.assign]], the one thing that sets it. */
    def rewriteSources(bank: TermBank): Array[RewriteSource] =
      if _rewriteSources == null then _rewriteSources = Superposition.rewriteSources(bank, this)
      _rewriteSources

    override def toString: String = if isEmpty then "□" else literals.mkString("[", ", ", "]")

  // --- Unification (Trail) --------------------------------------------------------------------------------

  /** Unification and matching over a [[TermBank]]. An operand is a `(term, scope)` pair, where the scope, `0`
    * or `1`, says which clause the variable belongs to, so that two clauses can share variable numbers without
    * being renamed. Arena terms are never mutated.
    *
    * No operation cleans up after itself. A caller brackets an attempt with `val s = save(); …; restore(s)`,
    * on both the success and the failure path. */
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

    /** Follow bindings from `(t, s)` to an unbound variable or a non-variable. The result is packed into one
     *  `Long` rather than a tuple. Ground results take [[GroundScope]], so identical ground terms compare
     *  equal in [[unify]] whatever scope they arrived in. */
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

    /** Unify `(t1, s1)` with `(t2, s2)`, leaving the bindings on the trail. On failure partial bindings
     *  remain, so the caller must restore either way. */
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

    /** Match `(pat, ps)` onto `(tgt, ts)`, binding only pattern-scope variables and treating the target as
      * rigid. Same trail protocol as [[unify]]. Cheaper than unification: target variables never bind, so there
      * are no chains to follow and no occurs check is needed.
      *
      * The target scope must carry no live bindings, which is asserted. A bound target variable is never
      * dereferenced, so such a binding would be silently mismatched and subsumption would become unsound. */
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

    def applier(): Applier = new Applier

    /** Instantiates operands under the current bindings, renaming each distinct unbound variable to a fresh
     *  dense number consistently across all calls, so one conclusion's literals share a coherent numbering. */
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

      /** Copy every literal of `lits` except index `skip` into `out` from index `from`, instantiated in scope
       *  `s`; returns the next free index. This is how every generating rule copies its surviving literals. */
      def copyLitsExcept(lits: Array[Literal], skip: Int, s: Scope, out: Array[Literal], from: Int): Int =
        var n = from
        var k = 0
        while k < lits.length do { if k != skip then { out(n) = applyLit(lits(k), s); n += 1 }; k += 1 }
        n

  // --- small helpers --------------------------------------------------------------------------------------

  private val EmptyArgs: Array[Int] = Array.empty[Int]

  /** Encode variable number `v` as a (negative) functor field. */
  private inline def encodeVar(v: Int): Int = -(v + 1)

  /** Decode a (negative) functor field back to a variable number. */
  private inline def decodeVar(fc: Int): Int = -fc - 1

  /** The free-variable-mask bit for variable number `v` (the overflow bit for `v >= 63`). */
  private inline def varBit(v: Int): Long = if v < 63 then 1L << v else FvOverflow
