package lisa.automation.superposition

import scala.collection.mutable

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
object Core {

  /** A reference to a term: the offset of its record in a [[TermBank]]'s arena. */
  opaque type Term = Int

  /** A literal: an atom [[Term]] together with a polarity, packed as `(atom << 1) | sign`. */
  opaque type Literal = Long

  /** A symbol code as handed out by a [[Signature]] (always `>= 0`); this is what a term stores as its head. */
  type Symbol = Int

  /**
   * The data for one interned symbol: immutable identity (`name`, `arity`, kind) and the
   * mutable ordering parameters used by KBO (`weight` and `precedence`). One instance is
   * allocated per distinct symbol. Terms refer to a symbol by its integer [[Symbol]] code
   * (`id`), so the hot paths index an array of these rather than dereferencing the object.
   */
  final class SymbolInfo private[Core] (val id: Symbol, val name: String, val arity: Int, val isPredicate: Boolean) {
    var weight: Int = 1
    var precedence: Int = id
    override def toString: String = s"$name/$arity"
  }

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
  final class Signature {
    private val infos: mutable.ArrayBuffer[SymbolInfo] = mutable.ArrayBuffer.empty[SymbolInfo]
    private val index: mutable.HashMap[(String, Int), Symbol] = mutable.HashMap.empty[(String, Int), Symbol]

    /** Default Knuth-Bendix weight given to a freshly interned symbol. */
    val defaultSymbolWeight: Int = 1

    /** Intern `(name, arity)`, returning its (stable) symbol code. */
    def intern(name: String, arity: Int, isPredicate: Boolean): Symbol =
      index.getOrElseUpdate((name, arity), {
        val info = new SymbolInfo(infos.length, name, arity, isPredicate)
        info.weight = defaultSymbolWeight
        infos += info
        info.id
      })

    /** Number of distinct symbols interned so far. */
    def size: Int = infos.length

    /** The full record for symbol `f`. */
    def info(f: Symbol): SymbolInfo = infos(f)

    def name(f: Symbol): String = infos(f).name
    def arity(f: Symbol): Int = infos(f).arity
    def isPredicate(f: Symbol): Boolean = infos(f).isPredicate

    def weight(f: Symbol): Int = infos(f).weight
    def setWeight(f: Symbol, w: Int): Unit = infos(f).weight = w

    def precedence(f: Symbol): Int = infos(f).precedence
    def setPrecedence(f: Symbol, p: Int): Unit = infos(f).precedence = p

    /** Compare two symbols by precedence: negative if `f < g`, positive if `f > g`, `0` if equal. */
    def comparePrecedence(f: Symbol, g: Symbol): Int = Integer.compare(infos(f).precedence, infos(g).precedence)
  }

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
   * offset of that record. This is the AoS layout used by Vampire/E (header fields followed
   * by inline children), but with all terms concatenated into one array and offsets used in
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
   * Hash-consing uses a custom open-addressing table that stores term offsets (`-1` =
   * empty); a slot is hashed and compared by reading the record it points at, so no key
   * object is ever materialised. Interning is write-first: a candidate record is appended
   * at the bump pointer so it can be compared by offset like any stored entry; on a hit the
   * bump pointer is rewound, on a miss the offset is kept and inserted.
   */
  final class TermBank(val signature: Signature) {

    private inline val HeaderWords = 3

    // --- arena ----------------------------------------------------------------------------
    private var mem: Array[Long] = new Array[Long](1024)
    private var end: Int = 0 // bump pointer: next free arena slot

    // --- hash-consing table (open addressing over term offsets, -1 = empty) ---------------
    private var htable: Array[Int] = Array.fill(1024)(-1)
    private var htMask: Int = htable.length - 1
    private var htCount: Int = 0

    private var clauseCounter: Int = 0

    /** Number of distinct terms stored. */
    def size: Int = htCount

    // --- constructors ---------------------------------------------------------------------

    /** The shared term for variable number `v` (`v >= 0`). */
    def mkVar(v: Int): Term = {
      require(v >= 0, s"variable number must be non-negative, got $v")
      ensureMem(HeaderWords)
      val p = end
      mem(p) = encodeVar(v).toLong & 0xFFFFFFFFL // arity 0, so high word is 0
      mem(p + 1) = varBit(v)
      mem(p + 2) = VariableWeight.toLong
      end = p + HeaderWords
      internCandidate(p)
    }

    /** A nullary symbol application, i.e. a constant. */
    def mkConst(f: Symbol): Term = mkApp(f, EmptyArgs)

    /** Apply symbol `f` to `children`. The array is read but not retained. */
    def mkApp(f: Symbol, children: Array[Term]): Term = {
      require(f >= 0, s"symbol code must be non-negative, got $f")
      val n = children.length
      require(n == signature.arity(f), s"arity mismatch for ${signature.name(f)}: expected ${signature.arity(f)}, got $n")
      ensureMem(HeaderWords + n)
      val p = end
      var mask = 0L
      var w = signature.weight(f)
      var i = 0
      while (i < n) {
        val c = children(i)
        mask |= mem(c + 1)
        w += mem(c + 2).toInt
        mem(p + HeaderWords + i) = c.toLong
        i += 1
      }
      mem(p) = (f.toLong & 0xFFFFFFFFL) | (n.toLong << 32)
      mem(p + 1) = mask
      mem(p + 2) = w.toLong & 0xFFFFFFFFL
      end = p + HeaderWords + n
      internCandidate(p)
    }

    // --- accessors ------------------------------------------------------------------------

    /** Raw functor field: `< 0` for variables, the symbol code otherwise. */
    def functor(t: Term): Int = mem(t).toInt // low 32 bits, sign-extended

    def isVar(t: Term): Boolean = mem(t).toInt < 0

    /** Variable number of a variable term (undefined for non-variables). */
    def varNum(t: Term): Int = decodeVar(mem(t).toInt)

    /** Head symbol of a compound/constant term (undefined for variables). */
    def headSymbol(t: Term): Symbol = mem(t).toInt

    /** Number of arguments (`0` for variables and constants). */
    def arity(t: Term): Int = (mem(t) >>> 32).toInt

    /** The `i`-th argument of `t`. */
    def arg(t: Term, i: Int): Term = mem(t + HeaderWords + i).toInt

    /** A fresh array with the children of `t`. */
    def args(t: Term): Array[Term] = {
      val n = arity(t)
      val out = new Array[Int](n)
      var i = 0
      while (i < n) {
        out(i) = mem(t + HeaderWords + i).toInt
        i += 1
      }
      out
    }

    /** Cached total KBO weight of `t`. */
    def weight(t: Term): Int = mem(t + 2).toInt

    /** Cached free-variable mask of `t` (see the object docs for the encoding). */
    def freeVarMask(t: Term): Long = mem(t + 1)

    /** A term is ground iff it has no free variables. */
    def isGround(t: Term): Boolean = mem(t + 1) == 0L

    /** Whether variable number `v` occurs in `t`; exact via the mask, with a traversal fallback for `v >= 63`. */
    def containsVar(t: Term, v: Int): Boolean = {
      val m = mem(t + 1)
      if (v < 63) (m & (1L << v)) != 0L
      else if ((m & FvOverflow) == 0L) false
      else traverseContains(t, v)
    }

    /** The smallest variable number occurring in `t`, or `-1` if `t` is ground; needs a traversal if only overflow vars occur. */
    def firstVar(t: Term): Int = {
      val m = mem(t + 1)
      val low = m & ~FvOverflow
      if (low != 0L) java.lang.Long.numberOfTrailingZeros(low)
      else if ((m & FvOverflow) == 0L) -1
      else traverseFirstVar(t, Int.MaxValue)
    }

    private def traverseContains(t: Term, v: Int): Boolean =
      if (isVar(t)) varNum(t) == v
      else {
        val n = arity(t)
        var i = 0
        while (i < n) {
          if (traverseContains(arg(t, i), v)) return true
          i += 1
        }
        false
      }

    private def traverseFirstVar(t: Term, best: Int): Int =
      if (isVar(t)) math.min(best, varNum(t))
      else {
        val n = arity(t)
        var b = best
        var i = 0
        while (i < n) {
          b = traverseFirstVar(arg(t, i), b)
          i += 1
        }
        b
      }

    // --- literals -------------------------------------------------------------------------

    /** Build a literal from an atom and a polarity. */
    def mkLiteral(atom: Term, positive: Boolean): Literal = (atom.toLong << 1) | (if (positive) 1L else 0L)

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
     * Build a clause from literals, putting it in canonical form: literals are sorted and
     * de-duplicated. The clause caches its weight (sum of literal weights) and gets a fresh
     * id. The empty clause (`Array.empty`) denotes falsity.
     */
    def mkClause(lits: Array[Literal]): Clause = {
      val sorted = lits.distinct.sorted
      var w = 0
      var i = 0
      while (i < sorted.length) {
        w += literalWeight(sorted(i))
        i += 1
      }
      val id = clauseCounter
      clauseCounter += 1
      new Clause(sorted, w, id)
    }

    /** A clause is a tautology if it contains a literal and its complement. */
    def isTautology(c: Clause): Boolean = {
      val lits = c.literals
      val seen = mutable.HashSet.empty[Literal]
      var i = 0
      while (i < lits.length) {
        if (seen.contains(negate(lits(i)))) return true
        seen += lits(i)
        i += 1
      }
      false
    }

    /**
     * Rename the variables of a clause to the canonical numbering `0,1,2,...` in order of
     * first occurrence (left-to-right over its already-sorted literals). Alpha-equivalent
     * clauses produced this way become structurally identical, which later phases rely on
     * for subsumption. (Full normalisation modulo literal order is refined in Phase 2.)
     */
    def canonicalVars(c: Clause): Clause = {
      val remap = mutable.HashMap.empty[Int, Int]
      def go(t: Term): Term =
        if (isVar(t)) mkVar(remap.getOrElseUpdate(varNum(t), remap.size))
        else if (arity(t) == 0) t
        else {
          val n = arity(t)
          val out = new Array[Int](n)
          var changed = false
          var i = 0
          while (i < n) {
            val child = arg(t, i)
            val nc = go(child)
            out(i) = nc
            if (nc != child) changed = true
            i += 1
          }
          if (changed) mkApp(functor(t), out) else t
        }
      val renamed = c.literals.map(l => mkLiteral(go(atomOf(l)), isPositive(l)))
      mkClause(renamed)
    }

    // --- internals ------------------------------------------------------------------------

    /**
     * Look the record freshly written at offset `p` up in the hash-cons table. If an equal
     * record already exists, rewind the bump pointer (discarding `p`) and return it;
     * otherwise keep `p` and insert it.
     */
    private def internCandidate(p: Term): Term = {
      var idx = hashOf(p) & htMask
      while (htable(idx) != -1) {
        val e = htable(idx)
        if (equalRecords(e, p)) {
          end = p // rewind: discard the candidate we just wrote
          return e
        }
        idx = (idx + 1) & htMask
      }
      htable(idx) = p
      htCount += 1
      if (htCount * 4 > (htMask + 1) * 3) resizeTable()
      p
    }

    /** Hash a term by its identifying words (functor + arity, then children). */
    private def hashOf(t: Term): Int = {
      var h = mem(t).toInt * 31 + (mem(t) >>> 32).toInt
      val n = (mem(t) >>> 32).toInt
      var i = 0
      while (i < n) {
        h = h * 31 + mem(t + HeaderWords + i).toInt
        i += 1
      }
      h ^= (h >>> 16)
      h
    }

    /** Structural equality of two records by reading the arena (functor+arity, then children). */
    private def equalRecords(a: Term, b: Term): Boolean =
      if (mem(a) != mem(b)) false // packs functor + arity, so this compares both at once
      else {
        val n = (mem(a) >>> 32).toInt
        var i = 0
        while (i < n) {
          if (mem(a + HeaderWords + i) != mem(b + HeaderWords + i)) return false
          i += 1
        }
        true
      }

    private def resizeTable(): Unit = {
      val newCap = (htMask + 1) * 2
      val nt = Array.fill(newCap)(-1)
      val nm = newCap - 1
      var i = 0
      while (i <= htMask) {
        val e = htable(i)
        if (e != -1) {
          var idx = hashOf(e) & nm
          while (nt(idx) != -1) idx = (idx + 1) & nm
          nt(idx) = e
        }
        i += 1
      }
      htable = nt
      htMask = nm
    }

    private def ensureMem(extra: Int): Unit =
      if (end + extra > mem.length) {
        var nl = mem.length * 2
        while (nl < end + extra) nl *= 2
        mem = java.util.Arrays.copyOf(mem, nl)
      }
  }

  // -----------------------------------------------------------------------------------------
  // Clause
  // -----------------------------------------------------------------------------------------

  /**
   * A clause is a multiset of [[Literal]]s in canonical (sorted, de-duplicated) order. It
   * caches its weight and carries a unique id for later age-based selection. An empty
   * literal array denotes the empty clause (falsity).
   */
  final class Clause private[Core] (val literals: Array[Literal], val weight: Int, val id: Int) {
    def size: Int = literals.length
    def isEmpty: Boolean = literals.length == 0

    override def toString: String = if (isEmpty) "□" else literals.mkString("[", ", ", "]")
  }

  // -----------------------------------------------------------------------------------------
  // small helpers
  // -----------------------------------------------------------------------------------------

  private val EmptyArgs: Array[Int] = Array.empty[Int]

  /** Encode variable number `v` as a (negative) functor field. */
  private inline def encodeVar(v: Int): Int = -(v + 1)

  /** Decode a (negative) functor field back to a variable number. */
  private inline def decodeVar(fc: Int): Int = -fc - 1

  /** The free-variable-mask bit for variable number `v` (the overflow bit for `v >= 63`). */
  private inline def varBit(v: Int): Long = if (v < 63) 1L << v else FvOverflow
}
