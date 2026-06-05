package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.interface.{ADT, Constructor}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.TypingHelpers
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.TypingHelpers.given
import lisa.maths.SetTheory.Types.ADTv2.support.core.QuantifiersIntro
import lisa.utils.prooflib.BasicStepTactic.{LeftExists, LeftOr, RightForall}
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

/**
 * Step 2: real LISA proof generators that fold over the nested-pattern decision
 * trie (see [[NestedTrie]]) and produce kernel-checked `THM`s.
 *
 *   - [[incompatibleProof]] : `binderTypings |- ¬(pattern_i = pattern_j)`
 *       via shared-constructor injectivity peeling + cross-constructor
 *       injectivity at the divergence point. KERNEL-CHECKED.
 *   - [[coverageProof]]     : `∀ x :: D. ⋁_clause ∃ binders. x = pattern_clause`
 *       recursive elimination over the trie. KERNEL-CHECKED.
 *
 * Patterns retain their real `Constructor`/`Variable` objects so generated terms
 * match what the eliminators speak about.
 */
object NestedTrieProofs {

  enum RPat:
    case RVar(v: Variable[Ind])
    case RCon(c: Constructor[?], args: List[RPat])
  import RPat.*

  type Ty = (ADT[?], Seq[Expr[Ind]])

  private def allConstructors: Seq[Constructor[?]] =
    ADT.allADTs.toSeq.flatMap(_.constructors)

  private def peelApp(t: Expr[Ind]): (Expr[Ind], List[Expr[Ind]]) =
    TypingHelpers.`*`.unapply(t) match
      case Some((f, x)) => val (h, as) = peelApp(f); (h, as :+ x)
      case None         => (t, Nil)

  def parse(term: Expr[Ind]): RPat =
    term match
      case v: Variable[Ind] @unchecked => RVar(v)
      case _ =>
        val (h, valueArgs) = peelApp(term)
        h match
          case Multiapp(c: Constant[?] @unchecked, _) =>
            allConstructors.find(_.id == c.id) match
              case Some(ctor) => RCon(ctor, valueArgs.takeRight(ctor.semantic.arity).map(parse))
              case None       => RVar(variable[Ind])
          case _ => RVar(variable[Ind])

  private def childTypes(c: Constructor[?], targs: Seq[Expr[Ind]]): Seq[Option[Ty]] =
    val subst = c.semantic.adt.typeVariablesSeq.zip(targs).map((v, a) => v := a)
    c.semantic.semanticSignature2.map { case (_, tyTerm) =>
      ADT.unapply(tyTerm.substitute(subst*).asInstanceOf[Expr[Ind]])
    }

  def termOf(p: RPat, ty: Ty): Expr[Ind] = p match
    case RVar(v) => v
    case RCon(c, args) =>
      val cts = childTypes(c, ty._2)
      appSeq(c.semantic.term(ty._2))(args.zip(cts).map((a, ct) => termOf(a, ct.get)))

  def bindersOf(p: RPat): List[Variable[Ind]] = p match
    case RVar(v)       => List(v)
    case RCon(_, args) => args.flatMap(bindersOf)

  // (variable, typeTerm) for every binder of a pattern — the typing hypotheses.
  private def bindersTyped(p: RPat, ty: Ty): Seq[(Expr[Ind], Expr[Ind])] = p match
    case RVar(v)       => Seq((v, ty._1.termAt(ty._2)))
    case RCon(c, args) =>
      val cts = childTypes(c, ty._2)
      args.zip(cts).flatMap((a, ct) => bindersTyped(a, ct.get))

  def divergePath(p: RPat, q: RPat): Option[List[Int]] = (p, q) match
    case (RCon(c, _), RCon(d, _)) if c.id != d.id => Some(Nil)
    case (RCon(_, as), RCon(_, bs)) =>
      as.lazyZip(bs).zipWithIndex.iterator
        .map { case ((a, b), i) => divergePath(a, b).map(i :: _) }
        .collectFirst { case Some(path) => path }
    case _ => None

  // Type-argument-aware accessors for the injectivity theorems. The cross-version
  // captures the ADT's arity so the two constructors line up with `injectivity`.
  private def crossInj(adt: ADT[?], c: Constructor[?], d: Constructor[?], targs: Seq[Expr[Ind]]): THM =
    adt match
      case a: ADT[n] =>
        val cc = c.asInstanceOf[Constructor[n]]
        val dd = d.asInstanceOf[Constructor[n]]
        if targs.isEmpty then a.injectivity(cc, dd) else a.injectivity(cc, dd, targs.head, targs.tail*)
  private def sameInj(c: Constructor[?], targs: Seq[Expr[Ind]]): THM =
    if targs.isEmpty then c.injectivity else c.injectivity(targs.head, targs.tail*)

  // ════════════════════════════════════════════════════════════════════════
  //  Disjointness:  binderTypings |- ¬(pattern_i === pattern_j)
  // ════════════════════════════════════════════════════════════════════════
  def incompatibleProof(domain: Ty, p: RPat, q: RPat): THM =
    val path = divergePath(p, q).getOrElse(
      throw new IllegalArgumentException("incompatibleProof: patterns are compatible (overlap).")
    )
    val tp = termOf(p, domain)
    val tq = termOf(q, domain)
    val typedHyps = wellTypedSet(bindersTyped(p, domain) ++ bindersTyped(q, domain)).toSeq

    Lemma((typedHyps |- !(tp === tq))) { sp ?=>
      typedHyps.foreach(h => assume(h))

      // Instantiate the outer ∀-prefix of `thm` with `terms`; leaves the body fact.
      def instAll(thm: THM, terms: Seq[Expr[Ind]]): Unit =
        var fact: sp.Fact = have(thm.statement.right.head) by Tautology.from(thm)
        terms.foreach { t =>
          fact.statement.right.head match
            case forall(qv, phi) =>
              fact = have(phi.substituteUnsafe(Map(qv -> t)).asInstanceOf[Expr[Prop]]) by
                InstantiateForall(t)(fact)
            case _ => ()
        }

      // Proves `termOf(p) :: type`: variables from the assumed hypotheses,
      // constructor applications from `introApp` (recursively on the arguments).
      def typeProof(p: RPat, ty: Ty): sp.Fact =
        val goal = termOf(p, ty) :: ty._1.termAt(ty._2)
        p match
          case RVar(_) => have(goal) by Tautology
          case RCon(c, args) =>
            val cts      = childTypes(c, ty._2)
            val argFacts = args.zip(cts).map((a, t) => typeProof(a, t.get))
            val intro    = if ty._2.isEmpty then c.introApp else c.introApp(ty._2.head, ty._2.tail*)
            val substs   = c.semantic.variables.zip(args.map(termOf(_, ty))).map((v, t) => v := t)
            val introInst: sp.Fact = if substs.isEmpty then intro else intro.of(substs*)
            have(goal) by Tautology.from((introInst +: argFacts)*)

      def typings(args: List[RPat], cts: Seq[Option[Ty]]): Seq[sp.Fact] =
        args.zip(cts).map((a, t) => typeProof(a, t.get))

      // Leaves `¬(termOf(p) === termOf(q))` as the latest fact.
      def disprove(p: RPat, q: RPat, ty: Ty, path: List[Int]): Unit =
        val tpc = termOf(p, ty); val tqc = termOf(q, ty)
        // Build each argument's term at its OWN (child) type, not the parent's.
        def argTermsAt(args: List[RPat], cts: Seq[Option[Ty]]): Seq[Expr[Ind]] =
          args.zip(cts).map((a, t) => termOf(a, t.get))
        (p, q) match
          case (RCon(c, as), RCon(d, bs)) if path.isEmpty =>
            // cross-constructor injectivity:  typed ⇒ ¬(c(..) === d(..))
            val ctsC = childTypes(c, ty._2); val ctsD = childTypes(d, ty._2)
            instAll(crossInj(ty._1, c, d, ty._2), argTermsAt(as, ctsC) ++ argTermsAt(bs, ctsD))
            val injInst = lastStep
            val argTypings = typings(as, ctsC) ++ typings(bs, ctsD)
            have(!(tpc === tqc)) by Tautology.from((injInst +: argTypings)*)
          case (RCon(c, as), RCon(_, bs)) =>
            val i   = path.head
            val cts = childTypes(c, ty._2)
            disprove(as(i), bs(i), cts(i).get, path.tail)
            val argDiseq = lastStep
            // same-head injectivity:  typed ⇒ ((c(as) === c(bs)) <=> (as === bs))
            instAll(sameInj(c, ty._2), argTermsAt(as, cts) ++ argTermsAt(bs, cts))
            val injInst = lastStep
            val argTypings = typings(as, cts) ++ typings(bs, cts)
            have(!(tpc === tqc)) by Tautology.from((injInst +: argDiseq +: argTypings)*)
          case _ => throw new IllegalArgumentException("disprove: malformed path.")

      disprove(p, q, domain, path)
      have(thesis) by Tautology.from(lastStep)
    }

  // ════════════════════════════════════════════════════════════════════════
  //  Coverage:  ∀ x :: D. ⋁_clause ∃ binders. x = pattern_clause
  // ════════════════════════════════════════════════════════════════════════
  // Recursive elimination over the trie. Each occurrence gets a deterministic
  // fresh variable `fv(occ)` used both as the eliminator witness and as the
  // clause binder in the target, so nested same-constructor levels never capture.
  // At each Switch: instantiate `adt.elim(targs)` at the occurrence value, split
  // its constructor disjunction, alpha-rename each disjunct's witnesses to the
  // occurrence's `fv`, `LeftExists` them, and recurse; each Leaf rebuilds
  // `x = pattern` by `Congruence` over the chained `value = c(children)`
  // equalities and closes its disjunct with `QuantifiersIntro`.
  //
  // Restriction: every clause binder must sit at a *leaf* occurrence of the
  // decision tree (no clause has a variable at a switched column). This holds for
  // any exhaustive, pairwise-disjoint set whose clauses discriminate before they
  // bind — i.e. the sets the system accepts.
  private final case class ColP(occ: List[Int], value: Expr[Ind], ty: Ty)
  private final case class RowP(pats: List[RPat], clause: Int)

  private def peelExists(f: Expr[Prop]): (List[Variable[Ind]], Expr[Prop]) = f match
    case ∃(v: Variable[Ind] @unchecked, body: Expr[Prop] @unchecked) =>
      val (vs, b) = peelExists(body); (v :: vs, b)
    case _ => (Nil, f)

  private def flatOr(f: Expr[Prop]): List[Expr[Prop]] = f match
    case a \/ b => flatOr(a) ++ flatOr(b)
    case _      => List(f)

  def coverageProof(domain: Ty, clauses: Seq[(Constructor[?], Seq[Expr[Ind]])]): THM =
    val x     = Variable[Ind]("scrutX")
    val dTerm = domain._1.termAt(domain._2)
    val pats  = clauses.map((c, args) => RCon(c, args.map(parse).toList)).toList

    // Deterministic, per-occurrence fresh variable (distinct names, no capture).
    val fvMemo = scala.collection.mutable.Map[List[Int], Variable[Ind]]()
    def fv(occ: List[Int]): Variable[Ind] =
      fvMemo.getOrElseUpdate(occ, Variable[Ind](s"fv${fvMemo.size}"))
    def valueAt(occ: List[Int]): Expr[Ind] = if occ.isEmpty then x else fv(occ)

    // Target term / binders for a clause, using fv at binder occurrences.
    def recon(p: RPat, ty: Ty, occ: List[Int]): Expr[Ind] = p match
      case RVar(_)       => fv(occ)
      case RCon(c, args) =>
        val cts = childTypes(c, ty._2)
        appSeq(c.semantic.term(ty._2))(
          args.zip(cts).zipWithIndex.map { case ((a, ct), i) => recon(a, ct.get, occ :+ i) })
    def binderVars(p: RPat, occ: List[Int]): List[Variable[Ind]] = p match
      case RVar(_)       => List(fv(occ))
      case RCon(_, args) => args.zipWithIndex.flatMap((a, i) => binderVars(a, occ :+ i))

    val disjuncts = pats.map(p => existsSeq(binderVars(p, Nil), x === recon(p, domain, Nil)))
    val bigOr     = seqOr(disjuncts)

    def switchIdx(cols: List[ColP], rows: List[RowP]): Option[Int] =
      cols.indices.find(j => rows.exists(_.pats(j) match { case RCon(_, _) => true; case _ => false }))

    Lemma(∀(x :: dTerm, bigOr)) {
      // `using proof` so each (possibly nested) call binds to the right proof.
      // `eqForms` carries the chained `value === c(children)` equalities of the
      // path (each a conjunct of an assumed body), re-derived as facts at the leaf.
      def cover(cols: List[ColP], rows: List[RowP], eqForms: List[Expr[Prop]])(using
          proof: lisa.SetTheoryLibrary.Proof): Unit =
        switchIdx(cols, rows) match
          case None =>
            val r       = rows.head
            val eqFacts = eqForms.map(ef => have(ef) by Tautology)
            have(x === recon(pats(r.clause), domain, Nil)) by Congruence.from(eqFacts*)
            have(disjuncts(r.clause)) by QuantifiersIntro(binderVars(pats(r.clause), Nil))(lastStep)
            have(bigOr) by Tautology.from(lastStep)
          case Some(j) =>
            val col = cols(j); val (adt, targs) = col.ty; val v = col.value
            val elimThm = if targs.isEmpty then adt.elim else adt.elim(targs.head, targs.tail*)
            val implForm = elimThm.statement.right.head match
              case forall(y, body) => body.substituteUnsafe(Map(y -> v)).asInstanceOf[Expr[Prop]]
            val inst    = have(implForm) by InstantiateForall(v)(elimThm)
            val isCv    = implForm match { case _ ==> concl => concl }
            val disjFact = have(isCv) by Tautology.from(inst)

            // One branch fact `renamedDisjunct |- bigOr` per constructor disjunct.
            // The disjuncts are in `adt.constructors` order, so we can zip them.
            val branchFacts = flatOr(isCv).zip(adt.constructors).map { (d, c) =>
              val (evars, body) = peelExists(d)
              val cts      = childTypes(c, targs)
              val freshArg = (0 until c.semantic.arity).map(i => fv(col.occ :+ i)).toList
              val rename   = evars.zip(freshArg).toMap.asInstanceOf[Map[Variable[?], Expr[?]]]
              val bodyR    = if rename.isEmpty then body else body.substituteUnsafe(rename).asInstanceOf[Expr[Prop]]

              // child columns/rows
              val childCols = freshArg.indices.map(i =>
                ColP(col.occ :+ i, fv(col.occ :+ i), cts(i).get)).toList
              val childRows = rows.flatMap { rr =>
                rr.pats(j) match
                  case RCon(cc, as) if cc.id == c.id => Some(RowP(rr.pats.patch(j, as, 1), rr.clause))
                  case RCon(_, _)                    => None
                  case RVar(_)                       =>
                    Some(RowP(rr.pats.patch(j, List.fill(c.semantic.arity)(RVar(variable[Ind])), 1), rr.clause))
              }
              val newCols = cols.patch(j, childCols, 1)
              val newEq: Expr[Prop] = v === appSeq(c.semantic.term(targs))(freshArg)

              val matrixFact = have(bodyR |- bigOr) subproof {
                assume(bodyR)
                cover(newCols, childRows, eqForms :+ newEq)
                have(bigOr) by Tautology.from(lastStep)
              }
              // bind the fresh witnesses:  existsSeq(freshArg, bodyR) |- bigOr
              freshArg.reverse.foldLeft[proof.Fact](matrixFact) { (fact, w) =>
                thenHave(∃(w, fact.statement.left.head) |- bigOr) by LeftExists
              }
              lastStep
            }

            val combined =
              if branchFacts.size == 1 then have(isCv |- bigOr) by Tautology.from(branchFacts.head)
              else have(isCv |- bigOr) by LeftOr(branchFacts*)
            have(bigOr) by Tautology.from(disjFact, combined)

      have(x :: dTerm ==> bigOr) subproof {
        assume(x :: dTerm)
        cover(List(ColP(Nil, x, domain)), pats.zipWithIndex.map((p, i) => RowP(List(p), i)), Nil)
      }
      thenHave(∀(x :: dTerm, bigOr)) by RightForall
    }
}
