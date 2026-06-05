package ADTv2Examples.functions

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.API.`*`
import lisa.maths.SetTheory.Types.ADTv2.library.Bool.*
import lisa.maths.SetTheory.Types.ADTv2.library.List.*
import lisa.maths.SetTheory.Types.ADTv2.library.Nat.*
import lisa.maths.SetTheory.Types.ADTv2.library.Option.*
import lisa.maths.SetTheory.Types.ADTv2.library.*
import lisa.maths.SetTheory.Types.ADTv2.interface.{ADT, Constructor}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.NestedTrie
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.NestedTrieProofs
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.NestedTrieProofs.RPat

/**
 * Runs the real-typed nested-pattern scope checker (NestedTrie) against the live
 * nat / Option / List ADT definitions. No proofs — prints the decision trie and
 * the IN SCOPE / REJECTED verdict for each example.
 */
object NestedTrieDemo extends lisa.Main {

  private val k = variable[Ind]
  private val t = variable[Ind]

  // Each clause is its top constructor + the value-argument terms.
  type Clauses = Seq[(Constructor[?], Seq[Expr[Ind]])]

  // Guard terms are built with the `*` set-application operator, exactly as the
  // `Case(...)` DSL does (e.g. `succ * k` is `app(succ)(k)`); nullary guards are
  // the bare constructor symbols (`zero`, `nil`).
  private val z: Expr[Ind]        = zero
  private def s(p: Expr[Ind])     = succ * p

  private val examples: Seq[(String, ADT[?], Seq[Expr[Ind]], Clauses)] = Seq(
    ("isOptionZero", option, Seq(nat), Seq(
      (none, Seq.empty),
      (some, Seq(z)),
      (some, Seq(s(k))))),

    ("isGreaterThanOne", nat, Seq.empty, Seq(
      (zero, Seq.empty),
      (succ, Seq(z)),
      (succ, Seq(s(k))))),

    ("isGreaterThanTwo", nat, Seq.empty, Seq(
      (zero, Seq.empty),
      (succ, Seq(z)),
      (succ, Seq(s(z))),
      (succ, Seq(s(s(k)))))),

    // non-exhaustive: zero branch dropped
    ("missingZero", nat, Seq.empty, Seq(
      (succ, Seq(z)),
      (succ, Seq(s(k))))),

    // overlap: catch-all succ(k) collides with succ(zero)
    ("overlapping", nat, Seq.empty, Seq(
      (zero, Seq.empty),
      (succ, Seq(z)),
      (succ, Seq(k)))),

    // depth-2: split a list of nats on whether its head is zero (tail is a binder)
    ("listHeadZero", list, Seq(nat), Seq(
      (nil, Seq.empty),
      (cons, Seq(z, t)),
      (cons, Seq(s(k), t)))),
  )

  examples.foreach { (name, adt, typeArgs, clauses) =>
    println(NestedTrie.analyze(name, adt, typeArgs, clauses))
  }

  // ── Step 2: kernel-checked disjointness proofs ─────────────────────────────
  private def cl(c: Constructor[?], args: Expr[Ind]*): RPat =
    RPat.RCon(c, args.map(NestedTrieProofs.parse).toList)

  private val natTy = (nat, Seq.empty[Expr[Ind]])
  private val optTy = (option, Seq[Expr[Ind]](nat))

  // (domain, label, p, q) for several disjoint pairs at varying divergence depth.
  private val disjointPairs = Seq(
    (natTy, "zero ⊥ succ(zero)            [root]",    cl(zero),        cl(succ, z)),
    (natTy, "succ(zero) ⊥ succ(succ k)    [depth 1]", cl(succ, z),     cl(succ, s(k))),
    (natTy, "succ(succ 0) ⊥ succ(succ(succ k)) [d2]", cl(succ, s(z)),  cl(succ, s(s(k)))),
    (optTy, "some(zero) ⊥ some(succ k)    [poly]",    cl(some, z),     cl(some, s(k))),
  )

  println("══════════ disjointness proofs (kernel-checked) ══════════")
  disjointPairs.foreach { (dom, label, p, q) =>
    val thm = NestedTrieProofs.incompatibleProof(dom, p, q)
    println(s"  ✓ $label\n      ⊢ ${thm.statement}")
  }

  // ── Step 2: kernel-checked coverage proofs ─────────────────────────────────
  private type Clause = (Constructor[?], Seq[Expr[Ind]])
  private val coverageCases: Seq[(String, (ADT[?], Seq[Expr[Ind]]), Seq[Clause])] = Seq(
    ("isGreaterThanOne", natTy, Seq((zero, Seq.empty), (succ, Seq(z)), (succ, Seq(s(k))))),
    ("isGreaterThanTwo", natTy, Seq((zero, Seq.empty), (succ, Seq(z)), (succ, Seq(s(z))), (succ, Seq(s(s(k)))))),
    ("isOptionZero",     optTy, Seq((none, Seq.empty), (some, Seq(z)), (some, Seq(s(k))))),
    ("listHeadZero",     (list, Seq[Expr[Ind]](nat)), Seq((nil, Seq.empty), (cons, Seq(z, t)), (cons, Seq(s(k), t)))),
  )

  println("══════════ coverage proofs (kernel-checked) ══════════")
  coverageCases.foreach { (label, dom, cls) =>
    val thm = NestedTrieProofs.coverageProof(dom, cls)
    println(s"  ✓ $label\n      ⊢ ${thm.statement}")
  }
}
