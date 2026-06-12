package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.interface.ADT
import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.ADTv2.support.core.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.altEqualityTransitivity
import lisa.maths.SetTheory.Types.TypingHelpers
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.BasicStepTactic.LeftExists
import lisa.utils.prooflib.BasicStepTactic.LeftOr
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.RightExists
import lisa.utils.prooflib.BasicStepTactic.RightForall
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
private[semantics] object NestedTrieProofs {

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

  def resolvedChildTypes(c: Constructor[?], targs: Seq[Expr[Ind]]): Seq[Option[Ty]] =
    childTypes(c, targs)

  def termOf(p: RPat, ty: Ty): Expr[Ind] = p match
    case RVar(v) => v
    case RCon(c, args) =>
      val cts = childTypes(c, ty._2)
      appSeq(c.semantic.term(ty._2))(args.zip(cts).map((a, ct) => termOf(a, ct.get)))

  def bindersOf(p: RPat): List[Variable[Ind]] = p match
    case RVar(v)       => List(v)
    case RCon(_, args) => args.flatMap(bindersOf)

  private def caseArgs(pp: NestedConstructorPattern[?]): Seq[Expr[Ind]] =
    (0 until pp.arity).map(i =>
      pp.guards.find(_.position == i).map(_.guardTerm).getOrElse(pp.topBinders(i))
    )

  private def renderCase(pp: NestedConstructorPattern[?]): String =
    val args = caseArgs(pp).map(arg => NestedTrie.show(NestedTrie.parsePat(arg)))
    if args.isEmpty then pp.semanticConstructor.name
    else s"${pp.semanticConstructor.name}(${args.mkString(", ")})"

  private def interfaceConstructor(pp: NestedConstructorPattern[?]): Constructor[?] =
    ADT.allADTs.toSeq
      .flatMap(_.constructors)
      .find(_.id == pp.semanticConstructor.id)
      .getOrElse(
        throw new IllegalArgumentException(
          s"No interface constructor found for ${pp.semanticConstructor.name}."
        )
      )

  private def renderAlignedGuards(
      p1: NestedConstructorPattern[?],
      p2: NestedConstructorPattern[?]
  ): String =
    val byPos1 = p1.guards.map(g => g.position -> g.guardTerm).toMap
    val byPos2 = p2.guards.map(g => g.position -> g.guardTerm).toMap
    val sharedPositions = byPos1.keySet.intersect(byPos2.keySet).toSeq.sorted
    if sharedPositions.isEmpty then "none"
    else
      sharedPositions.map { pos =>
        val left = NestedTrie.show(NestedTrie.parsePat(byPos1(pos)))
        val right = NestedTrie.show(NestedTrie.parsePat(byPos2(pos)))
        s"arg $pos: $left vs $right"
      }.mkString("; ")

  private def renderOverlapTrie(
      p1: NestedConstructorPattern[?],
      p2: NestedConstructorPattern[?]
  ): String =
    val (adt, targs) = ADT.unapply(p1.specializedAdtTerm).get
    val clauses = Seq(p1, p2).map(pp => (interfaceConstructor(pp), caseArgs(pp)))
    val tree = NestedTrie.buildTree(adt, targs, clauses)
    NestedTrie.render(tree)

  // (variable, typeTerm) for every binder of a pattern — the typing hypotheses.
  private def bindersTyped(p: RPat, ty: Ty): Seq[(Expr[Ind], Expr[Ind])] = p match
    case RVar(v)       => Seq((v, ty._1.termAt(ty._2)))
    case RCon(c, args) =>
      val cts = childTypes(c, ty._2)
      args.zip(cts).flatMap((a, ct) => bindersTyped(a, ct.get))

  /**
   * Free variables appearing inside a (possibly non-nullary, possibly nested)
   * guard term, paired with their resolved type terms. `argType` is the already
   * type-substituted ADT type term of the guarded argument position. Returns the
   * empty sequence for nullary / ground guards (`tru`, `succ(zero)`, …).
   */
  def guardBinders(term: Expr[Ind], argType: Expr[Ind]): Seq[(Variable[Ind], Expr[Ind])] =
    ADT.unapply(argType) match
      case Some(ty) => bindersTyped(parse(term), ty).map((t, tp) => (t.asInstanceOf[Variable[Ind]], tp))
      case None     => Seq.empty

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

  // The top constructor's injectivity for a pattern, specialized to its type args.
  // (Used directly so it is unaffected by a pattern's overridden `injectivity`.)
  def constructorInjectivity(pp: NestedConstructorPattern[?]): THM =
    val base = pp.semanticConstructor.injectivity
    if pp.typeSubstitutions.isEmpty then base
    else Lemma(base.statement.substitute(pp.typeSubstitutions*)) {
      have(thesis) by Restate.from(base.of(pp.typeSubstitutions*))
    }

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
            val implForm = (elimThm.statement.right.head: @unchecked) match
              case forall(y, body) => body.substituteUnsafe(Map(y -> v)).asInstanceOf[Expr[Prop]]
            val inst    = have(implForm) by InstantiateForall(v)(elimThm)
            val isCv    = (implForm: @unchecked) match { case _ ==> concl => concl }
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

  // Occurrences of the variable leaves of an RPat (left-to-right).
  private def rvarOccs(p: RPat, occ: List[Int]): List[List[Int]] = p match
    case RVar(_)       => List(occ)
    case RCon(_, args) => args.zipWithIndex.flatMap((a, i) => rvarOccs(a, occ :+ i)).toList

  // ════════════════════════════════════════════════════════════════════════
  //  Coverage in the trait `caseCoverage` shape:
  //    ∀ x :: D. simplify( ⋁_p ∃ p.variables2. (p.freshBranchPremise ∧ x=p.freshInputTerm) )
  //  Same recursion as `coverageProof`; only the leaf differs — it witnesses each
  //  pattern's `variables2` with the per-occurrence eliminator eigenvars.
  // ════════════════════════════════════════════════════════════════════════
  def coverageCaseShape(
      domain: Ty,
      clauses: Seq[(Constructor[?], Seq[Expr[Ind]])],
      patterns: Seq[Pattern[?]]
  ): THM =
    val x     = Variable[Ind]("scrutX")
    val dTerm = domain._1.termAt(domain._2)
    val pats  = clauses.map((c, args) => RCon(c, args.map(parse).toList)).toList

    val fvMemo = scala.collection.mutable.Map[List[Int], Variable[Ind]]()
    def fv(occ: List[Int]): Variable[Ind] =
      fvMemo.getOrElseUpdate(occ, Variable[Ind](s"fv${fvMemo.size}"))
    def valueAt(occ: List[Int]): Expr[Ind] = if occ.isEmpty then x else fv(occ)

    // The caseCoverage disjuncts, in pattern order, and their (simplified) ∨.
    val disjuncts = patterns.map(p =>
      existsSeq(p.variables2, p.freshBranchPremise /\ (x === p.freshInputTerm))).toList
    val bigOr = simplify(seqOr(disjuncts))

    def switchIdx(cols: List[ColP], rows: List[RowP]): Option[Int] =
      cols.indices.find(j => rows.exists(_.pats(j) match { case RCon(_, _) => true; case _ => false }))

    Lemma(∀(x :: dTerm, bigOr)) {
      def cover(cols: List[ColP], rows: List[RowP], eqForms: List[Expr[Prop]])(using
          proof: lisa.SetTheoryLibrary.Proof): Unit =
        switchIdx(cols, rows) match
          case None =>
            val r          = rows.head
            val p          = patterns(r.clause)
            val v2         = p.variables2.toList
            val deepOccs   = rvarOccs(pats(r.clause), Nil).filter(_.length >= 2)
            val wits: List[Expr[Ind]] =
              (0 until p.arity).map(i => valueAt(List(i))).toList ++ deepOccs.map(valueAt)
            val sub        = v2.zip(wits).map((from, to) => from := to)
            val body       = p.freshBranchPremise /\ (x === p.freshInputTerm)

            val eqFacts = eqForms.map(ef => have(ef) by Tautology)
            def proveByCongruence(formula: Expr[Prop]): proof.Fact =
              formula match
                case lhs /\ rhs =>
                  val leftFact = proveByCongruence(lhs)
                  val rightFact = proveByCongruence(rhs)
                  have(formula) by Tautology.from(leftFact, rightFact)
                case _ =>
                  have(formula) by Congruence.from(eqFacts*)
            // body at the chosen witnesses: typing from the context, equalities by Congruence.
            val inputEq = have((x === p.freshInputTerm).substitute(sub*)) by Congruence.from(eqFacts*)
            val condEq  = proveByCongruence(p.freshBranchCondition.substitute(sub*).asInstanceOf[Expr[Prop]])
            val typ     = have(p.freshTypingFormula.substitute(sub*).asInstanceOf[Expr[Prop]]) by Tautology
            have(body.substitute(sub*).asInstanceOf[Expr[Prop]]) by Tautology.from(inputEq, condEq, typ)
            // introduce the existentials over variables2 with these witnesses
            for k <- (v2.length - 1) to 0 by -1 do
              val goal = existsSeq(v2.drop(k),
                body.substitute(v2.take(k).zip(wits.take(k)).map((f, t) => f := t)*).asInstanceOf[Expr[Prop]])
              thenHave(goal) by RightExists
            have(bigOr) by Tautology.from(lastStep)
          case Some(j) =>
            val col = cols(j); val (adt, targs) = col.ty; val v = col.value
            val elimThm = if targs.isEmpty then adt.elim else adt.elim(targs.head, targs.tail*)
            val implForm = (elimThm.statement.right.head: @unchecked) match
              case forall(y, b) => b.substituteUnsafe(Map(y -> v)).asInstanceOf[Expr[Prop]]
            val inst    = have(implForm) by InstantiateForall(v)(elimThm)
            val isCv    = (implForm: @unchecked) match { case _ ==> concl => concl }
            val disjFact = have(isCv) by Tautology.from(inst)

            val branchFacts = flatOr(isCv).zip(adt.constructors).map { (d, c) =>
              val (evars, b) = peelExists(d)
              val cts      = childTypes(c, targs)
              val freshArg = (0 until c.semantic.arity).map(i => fv(col.occ :+ i)).toList
              val rename   = evars.zip(freshArg).toMap.asInstanceOf[Map[Variable[?], Expr[?]]]
              val bodyR    = if rename.isEmpty then b else b.substituteUnsafe(rename).asInstanceOf[Expr[Prop]]
              val childCols = freshArg.indices.map(i => ColP(col.occ :+ i, fv(col.occ :+ i), cts(i).get)).toList
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

  // ════════════════════════════════════════════════════════════════════════
  //  branchSelectionFor in the (multi-level) trait shape — inner binders bound:
  //    ∀ c.variables2. (typed ∧ term=c(vars2))
  //       ⟹ ⋁_{p of c} ∃ p.innerVars. (p.freshBranchCondition ∧ term=p.freshInputTerm)
  //  Proved by `cover` rooted at the guarded argument variable.
  // ════════════════════════════════════════════════════════════════════════
  def branchSelectionForCaseShape(
      cSem: SemanticConstructor[?],
      cInt: Constructor[?],
      term: Expr[Ind],
      patterns: Seq[NestedConstructorPattern[?]],
      typeSubst: Seq[lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution]
  ): THM =
    val arity   = cSem.arity
    val topVars = cSem.variables2.toList
    // Every argument position guarded by some pattern (ascending). The decision
    // trie is rooted at *all* of them, so guards on several arguments of the same
    // constructor (e.g. `cons(tru, nil)`) each get their equation threaded into
    // `eqForms`; rooting at only the first guard leaves the others unprovable.
    val guardPositions: List[Int] =
      patterns.flatMap(_.guards.map(_.position)).distinct.sorted.toList
    def guardTyAt(pos: Int): Ty =
      ADT.unapply(cSem.semanticSignature2(pos)._2.substitute(typeSubst*).asInstanceOf[Expr[Ind]]).get
    val typedPart = wellTypedFormula(cSem.semanticSignature2).substitute(typeSubst*).asInstanceOf[Expr[Prop]]
    val inputEqC  = (term === cSem.appliedTerm2).substitute(typeSubst*).asInstanceOf[Expr[Prop]]

    // Each clause's (fresh) guard terms, keyed by argument position. A clause that
    // does not guard a column carries the constructor's own binder there (an RVar,
    // so the trie never switches on it). Disjunct = ∃inner. (cond ∧ term=freshInput).
    def guardsByPos(p: NestedConstructorPattern[?]): Map[Int, RPat] =
      p.freshGuards.map(g => g.position -> parse(g.guardTerm)).toMap
    val innerVarsOf = patterns.map(p => p.variables2.drop(arity).toList)
    val disjuncts = patterns.map(p => p.branchSelectionDisjunct(term)).toList
    val bigOr = seqOr(disjuncts)

    // Root occurrences `List(pos)` resolve to the constructor's argument binders
    // (which `typedPart`/`inputEqC` speak about); deeper occurrences get fresh vars.
    val rootVars: Map[List[Int], Variable[Ind]] =
      guardPositions.map(pos => List(pos) -> cSem.variables2(pos)).toMap
    val fvMemo = scala.collection.mutable.Map[List[Int], Variable[Ind]]()
    def fv(occ: List[Int]): Variable[Ind] =
      rootVars.getOrElse(occ, fvMemo.getOrElseUpdate(occ, Variable[Ind](s"bsf${fvMemo.size}")))

    def switchIdx(cols: List[ColP], rows: List[RowP]): Option[Int] =
      cols.indices.find(j => rows.exists(_.pats(j) match { case RCon(_, _) => true; case _ => false }))

    Lemma(forallSeq(topVars, (typedPart /\ inputEqC) ==> bigOr)) {
      def cover(cols: List[ColP], rows: List[RowP], eqForms: List[Expr[Prop]])(using
          proof: lisa.SetTheoryLibrary.Proof): Unit =
        switchIdx(cols, rows) match
          case None =>
            val r        = rows.head
            val p        = patterns(r.clause)
            val inner    = innerVarsOf(r.clause)
            // Leaf occurrences across *all* of this clause's guards, prefixed by
            // each guard's position so they line up with the trie's `fv` keys (and
            // with `inner`, which lists the inner binders guard-by-guard in order).
            val occs     = p.freshGuards
              .flatMap(g => rvarOccs(parse(g.guardTerm), List(g.position))).toList
            val wits     = occs.map(fv(_): Expr[Ind])
            val sub      = inner.zip(wits).map((f, t) => f := t)
            val body     = p.branchSelectionBody(term)
            val eqFacts  = eqForms.map(ef => have(ef) by Tautology)
            def proveByCongruence(formula: Expr[Prop]): proof.Fact =
              formula match
                case lhs /\ rhs =>
                  val leftFact = proveByCongruence(lhs)
                  val rightFact = proveByCongruence(rhs)
                  have(formula) by Tautology.from(leftFact, rightFact)
                case _ =>
                  have(formula) by Congruence.from(eqFacts*)
            val condEq   = proveByCongruence(p.freshBranchCondition.substitute(sub*).asInstanceOf[Expr[Prop]])
            val inEq     = have(term === p.freshInputTerm) by Tautology
            // inner-binder typings come from the context (the eliminator's wellTyped conjuncts).
            have(body.substitute(sub*).asInstanceOf[Expr[Prop]]) by Tautology.from(condEq, inEq)
            for k <- (inner.length - 1) to 0 by -1 do
              val goal = existsSeq(inner.drop(k),
                body.substitute(inner.take(k).zip(wits.take(k)).map((f, t) => f := t)*).asInstanceOf[Expr[Prop]])
              thenHave(goal) by RightExists
            have(bigOr) by Tautology.from(lastStep)
          case Some(j) =>
            val col = cols(j); val (adt, targs) = col.ty; val v = col.value
            val elimThm = if targs.isEmpty then adt.elim else adt.elim(targs.head, targs.tail*)
            val implForm = (elimThm.statement.right.head: @unchecked) match
              case forall(y, b) => b.substituteUnsafe(Map(y -> v)).asInstanceOf[Expr[Prop]]
            val inst    = have(implForm) by InstantiateForall(v)(elimThm)
            val isCv    = (implForm: @unchecked) match { case _ ==> concl => concl }
            val disjFact = have(isCv) by Tautology.from(inst)
            val branchFacts = flatOr(isCv).zip(adt.constructors).map { (d, c) =>
              val (evars, b) = peelExists(d)
              val cts      = childTypes(c, targs)
              val freshArg = (0 until c.semantic.arity).map(i => fv(col.occ :+ i)).toList
              val rename   = evars.zip(freshArg).toMap.asInstanceOf[Map[Variable[?], Expr[?]]]
              val bodyR    = if rename.isEmpty then b else b.substituteUnsafe(rename).asInstanceOf[Expr[Prop]]
              val childCols = freshArg.indices.map(i => ColP(col.occ :+ i, fv(col.occ :+ i), cts(i).get)).toList
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
              freshArg.reverse.foldLeft[proof.Fact](matrixFact) { (fact, w) =>
                thenHave(∃(w, fact.statement.left.head) |- bigOr) by LeftExists
              }
              lastStep
            }
            val combined =
              if branchFacts.size == 1 then have(isCv |- bigOr) by Tautology.from(branchFacts.head)
              else have(isCv |- bigOr) by LeftOr(branchFacts*)
            have(bigOr) by Tautology.from(disjFact, combined)

      have((typedPart /\ inputEqC) ==> bigOr) subproof {
        assume(typedPart); assume(inputEqC)
        val rootCols = guardPositions.map(pos => ColP(List(pos), cSem.variables2(pos), guardTyAt(pos)))
        val rootRows = patterns.zipWithIndex.map { (p, i) =>
          val byPos = guardsByPos(p)
          RowP(guardPositions.map(pos => byPos.getOrElse(pos, RVar(cSem.variables2(pos)))), i)
        }.toList
        cover(rootCols, rootRows, Nil)
      }
      for vv <- topVars.reverse do
        thenHave(∀(vv, lastStep.statement.right.head)) by RightForall
      have(thesis) by Tautology.from(lastStep)
    }

  // ════════════════════════════════════════════════════════════════════════
  //  Disjointness in the trait shape:
  //    (p1.branchPremise1 ∧ p2.freshBranchPremise) ⟹ ¬(p1.inputTerm1 = p2.inputTerm2)
  //  Same outer structure as the existing nullary `incompatible`; the final
  //  guard-term disequality uses the recursive divergence peel instead.
  // ════════════════════════════════════════════════════════════════════════
  def incompatibleCaseShape(p1: NestedConstructorPattern[?], p2: NestedConstructorPattern[?]): THM =
    p1 match
      case p1c: NestedConstructorPattern[n] =>
        incompatibleCaseShapeN[n](p1c, p2.asInstanceOf[NestedConstructorPattern[n]])

  private def incompatibleCaseShapeN[N <: lisa.utils.prooflib.ProofTacticLib.Arity](
      p1: NestedConstructorPattern[N], p2: NestedConstructorPattern[N]
  ): THM =
    if p1.semanticConstructor != p2.semanticConstructor then
      // different top constructors — `¬(c1(top1) = c2(top2))` from cross injectivity.
      val (adt, targs) = ADT.unapply(p1.specializedAdtTerm).get
      val c1 = adt.constructors.find(_.id == p1.semanticConstructor.id).get
      val c2 = adt.constructors.find(_.id == p2.semanticConstructor.id).get
      val top1 = p1.variables1.take(p1.arity).map(x => x: Expr[Ind])
      val top2 = p2.variables2.take(p2.arity).map(x => x: Expr[Ind])
      Lemma((p1.branchPremise1 /\ p2.freshBranchPremise) ==> !(p1.inputTerm1 === p2.inputTerm2)) {
        val branch = assume(p1.branchPremise1 /\ p2.freshBranchPremise)
        val b1 = have(p1.branchPremise1) by Tautology.from(branch)
        val b2 = have(p2.freshBranchPremise) by Tautology.from(branch)
        val inj = crossInj(adt, c1, c2, targs)
        var fact = have(inj.statement.right.head) by Tautology.from(inj)
        (top1 ++ top2).foreach { t =>
          fact.statement.right.head match
            case forall(qv, phi) =>
              fact = have(phi.substituteUnsafe(Map(qv -> t)).asInstanceOf[Expr[Prop]]) by InstantiateForall(t)(fact)
            case _ => ()
        }
        have(!(p1.inputTerm1 === p2.inputTerm2)) by Tautology.from(fact, b1, b2)
      }
    else
      val guards1 = p1.guardsAt(p1.variables1)
      val guards2 = p2.freshGuards
      val selectedGuardsAndPath = guards1.zip(guards2).collectFirst {
        case (guard1, guard2)
            if guard1.position == guard2.position &&
              divergePath(parse(guard1.guardTerm), parse(guard2.guardTerm)).nonEmpty =>
          (
            guard1,
            guard2,
            divergePath(parse(guard1.guardTerm), parse(guard2.guardTerm)).get
          )
      }.getOrElse(
        throw new IllegalArgumentException(
          s"""incompatibleCaseShape rejected two overlapping nested cases for constructor ${p1.semanticConstructor.name}.
             |case 1: ${renderCase(p1)}
             |case 2: ${renderCase(p2)}
             |No divergent aligned guard pair was found, so the two cases still overlap.
             |Aligned guarded positions: ${renderAlignedGuards(p1, p2)}
             |Decision trie for the two cases:
             |${renderOverlapTrie(p1, p2)}""".stripMargin
        )
      )
      val (guard1, guard2, guardPath) = selectedGuardsAndPath
      val guardTy: Ty =
        val t = p1.semanticConstructor.semanticSignature2(guard1.position)._2
          .substitute(p1.typeSubstitutions*).asInstanceOf[Expr[Ind]]
        ADT.unapply(t).get

      Lemma(
        (p1.branchPremise1 /\ p2.freshBranchPremise) ==> !(p1.inputTerm1 === p2.inputTerm2)
      ) { sp ?=>
        // --- locals: instAll / typeProof / disprove on the guard terms ---
        def instAll(thm: THM, terms: Seq[Expr[Ind]]): Unit =
          var fact: sp.Fact = have(thm.statement.right.head) by Tautology.from(thm)
          terms.foreach { t =>
            fact.statement.right.head match
              case forall(qv, phi) =>
                fact = have(phi.substituteUnsafe(Map(qv -> t)).asInstanceOf[Expr[Prop]]) by
                  InstantiateForall(t)(fact)
              case _ => ()
          }
        def typeProof(p: RPat, ty: Ty): sp.Fact =
          val goal = termOf(p, ty) :: ty._1.termAt(ty._2)
          p match
            case RVar(_) => have(goal) by Tautology   // inner-binder typing from the branch premises
            case RCon(c, args) =>
              val cts      = childTypes(c, ty._2)
              val argFacts = args.zip(cts).map((a, t) => typeProof(a, t.get))
              val intro    = if ty._2.isEmpty then c.introApp else c.introApp(ty._2.head, ty._2.tail*)
              val substs   = c.semantic.variables.zip(args.map(termOf(_, ty))).map((v, t) => v := t)
              val introInst: sp.Fact = if substs.isEmpty then intro else intro.of(substs*)
              have(goal) by Tautology.from((introInst +: argFacts)*)
        def disprove(p: RPat, q: RPat, ty: Ty, path: List[Int]): Unit =
          val tpc = termOf(p, ty); val tqc = termOf(q, ty)
          (p, q) match
            case (RCon(c, as), RCon(d, bs)) if path.isEmpty =>
              val ctsC = childTypes(c, ty._2); val ctsD = childTypes(d, ty._2)
              instAll(crossInj(ty._1, c, d, ty._2),
                as.zip(ctsC).map((a, t) => termOf(a, t.get)) ++ bs.zip(ctsD).map((b, t) => termOf(b, t.get)))
              val injInst = lastStep
              val tys = as.zip(ctsC).map((a, t) => typeProof(a, t.get)) ++ bs.zip(ctsD).map((b, t) => typeProof(b, t.get))
              have(!(tpc === tqc)) by Tautology.from((injInst +: tys)*)
            case (RCon(c, as), RCon(_, bs)) =>
              val i = path.head; val cts = childTypes(c, ty._2)
              disprove(as(i), bs(i), cts(i).get, path.tail)
              val argDiseq = lastStep
              instAll(sameInj(c, ty._2),
                as.zip(cts).map((a, t) => termOf(a, t.get)) ++ bs.zip(cts).map((b, t) => termOf(b, t.get)))
              val injInst = lastStep
              val tys = as.zip(cts).map((a, t) => typeProof(a, t.get)) ++ bs.zip(cts).map((b, t) => typeProof(b, t.get))
              have(!(tpc === tqc)) by Tautology.from((injInst +: argDiseq +: tys)*)
            case _ => throw new IllegalArgumentException("disprove: malformed path.")

        // --- outer structure (mirrors the existing incompatible) ---
        val branch = assume(p1.branchPremise1 /\ p2.freshBranchPremise)
        val branch1Typed = have(p1.branchPremise1) by Tautology.from(branch)
        val branch2Typed = have(p2.freshBranchPremise) by Tautology.from(branch)
        assume(p1.inputTerm1 === p2.inputTerm2)
        val inputsEqual = have(p1.inputTerm1 === p2.inputTerm2) by Hypothesis

        val ctorInj = constructorInjectivity(p1)
        val injectivitySchema = have(ctorInj.statement.right.head) by Tautology.from(ctorInj)
        var injectivityAtVars = injectivitySchema
        for v <- p1.variables1.take(p1.arity) ++ p2.variables2.take(p2.arity) do
          injectivityAtVars.statement.right.head match
            case forall(qv, phi) =>
              injectivityAtVars = have(phi.substituteUnsafe(Map(qv -> v)).asInstanceOf[Expr[Prop]]) by
                InstantiateForall(v)(injectivityAtVars)
            case _ => ()

        val guardedArgsEqual = have(guard1.binder === guard2.binder) by
          Tautology.from(injectivityAtVars, branch1Typed, branch2Typed, inputsEqual)
        val guard1Eq = have(guard1.binder === guard1.guardTerm) by Tautology.from(branch1Typed)
        val guard2Eq = have(guard2.binder === guard2.guardTerm) by Tautology.from(branch2Typed)
        val guard1EqRev = have(guard1.guardTerm === guard1.binder) by Congruence.from(guard1Eq)
        val guard1ToGuard2Binder = have(guard1.guardTerm === guard2.binder) by Tautology.from(
          altEqualityTransitivity of (x := guard1.guardTerm, y := guard1.binder, z := guard2.binder),
          guard1EqRev, guardedArgsEqual)
        val guardTermsEqual = have(guard1.guardTerm === guard2.guardTerm) by Tautology.from(
          altEqualityTransitivity of (x := guard1.guardTerm, y := guard2.binder, z := guard2.guardTerm),
          guard1ToGuard2Binder, guard2Eq)

        // the new part: guard terms are distinct by the recursive peel
        val rp1 = parse(guard1.guardTerm); val rp2 = parse(guard2.guardTerm)
        disprove(rp1, rp2, guardTy, guardPath)
        have(thesis) by Tautology.from(guardTermsEqual, lastStep)
      }

  // ════════════════════════════════════════════════════════════════════════
  //  Pattern-level injectivity (well-definedness), the shape `samePatternBody
  //  Equality` consumes:
  //    ∀(v1 ++ v2). (branchPremise(v1) ∧ branchPremise(v2))
  //                  ⟹ ((inputTerm(v1) = inputTerm(v2)) ⇔ (v1 === v2))
  //  Forward direction uses the top constructor injectivity plus a recursive
  //  injective descent through the guard term (the mirror of `disprove`).
  // ════════════════════════════════════════════════════════════════════════
  def injectivityCaseShape(pp: NestedConstructorPattern[?]): THM =
    val v1 = pp.variables1.toList; val v2 = pp.variables2.toList
    val ar = pp.arity
    val (top1, inner1) = v1.splitAt(ar); val (top2, inner2) = v2.splitAt(ar)
    val A      = pp.inputTermAt(v1) === pp.inputTermAt(v2)
    val seqEqV = seqEq(v1, v2)
    val bp1 = pp.branchPremiseAt(v1); val bp2 = pp.branchPremiseAt(v2)
    val guards1 = pp.guardsAt(pp.variables1)
    val guards2 = pp.freshGuards
    val topInjThm: THM = constructorInjectivity(pp)

    Lemma(forallSeq(v1 ++ v2, (bp1 /\ bp2) ==> simplify(A <=> seqEqV))) {
      def instAll(thm: THM, terms: Seq[Expr[Ind]])(using proof: lisa.SetTheoryLibrary.Proof): Unit =
        var fact: proof.Fact = have(thm.statement.right.head) by Tautology.from(thm)
        terms.foreach { t =>
          fact.statement.right.head match
            case forall(qv, phi) =>
              fact = have(phi.substituteUnsafe(Map(qv -> t)).asInstanceOf[Expr[Prop]]) by InstantiateForall(t)(fact)
            case _ => ()
        }
      def typeProof(p: RPat, ty: Ty)(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
        val goal = termOf(p, ty) :: ty._1.termAt(ty._2)
        p match
          case RVar(_) => have(goal) by Tautology
          case RCon(c, args) =>
            val cts      = childTypes(c, ty._2)
            val argFacts = args.zip(cts).map((a, t) => typeProof(a, t.get))
            val intro    = if ty._2.isEmpty then c.introApp else c.introApp(ty._2.head, ty._2.tail*)
            val substs   = c.semantic.variables.zip(args.map(termOf(_, ty))).map((v, t) => v := t)
            val introInst: proof.Fact = if substs.isEmpty then intro else intro.of(substs*)
            have(goal) by Tautology.from((introInst +: argFacts)*)
      // From `termOf(rp1) = termOf(rp2)` derive the leaf (inner-binder) equalities,
      // indexed by the exact binder pair they justify.
      def injectEq(rp1: RPat, rp2: RPat, ty: Ty, eqFact: lisa.SetTheoryLibrary.Proof#Fact)(using
          proof: lisa.SetTheoryLibrary.Proof): Map[(Variable[Ind], Variable[Ind]), proof.Fact] =
        (rp1, rp2) match
          case (RVar(vl), RVar(vr)) => Map((vl, vr) -> eqFact.asInstanceOf[proof.Fact])
          case (RCon(c, as1), RCon(_, as2)) =>
            val cts = childTypes(c, ty._2)
            val t1  = as1.zip(cts).map((a, t) => termOf(a, t.get))
            val t2  = as2.zip(cts).map((a, t) => termOf(a, t.get))
            instAll(sameInj(c, ty._2), t1 ++ t2)
            val injInst = lastStep
            val tys = as1.zip(cts).map((a, t) => typeProof(a, t.get)) ++ as2.zip(cts).map((a, t) => typeProof(a, t.get))
            as1.indices.toList.foldLeft(Map.empty[(Variable[Ind], Variable[Ind]), proof.Fact]) { (acc, i) =>
              val argEq = have(t1(i) === t2(i)) by Tautology.from((injInst +: eqFact.asInstanceOf[proof.Fact] +: tys)*)
              acc ++ injectEq(as1(i), as2(i), cts(i).get, argEq.asInstanceOf[lisa.SetTheoryLibrary.Proof#Fact])
            }
          case _ => throw new IllegalArgumentException("injectEq: mismatched guard structure.")

      def topBinderEqualities(topEq: lisa.SetTheoryLibrary.Proof#Fact)(using
          proof: lisa.SetTheoryLibrary.Proof): Map[(Variable[Ind], Variable[Ind]), proof.Fact] =
        top1.zip(top2).map { (left, right) =>
          val eqFact: proof.Fact = have((left: Expr[Ind]) === (right: Expr[Ind])) by Tautology.from(topEq.asInstanceOf[proof.Fact])
          (left, right) -> eqFact
        }.toMap

      def orderedBinderEqualities(
          topEqMap: Map[(Variable[Ind], Variable[Ind]), lisa.SetTheoryLibrary.Proof#Fact],
          leafEqMap: Map[(Variable[Ind], Variable[Ind]), lisa.SetTheoryLibrary.Proof#Fact]
      )(using proof: lisa.SetTheoryLibrary.Proof): Seq[proof.Fact] =
        v1.zip(v2).map { (left, right) =>
          topEqMap
            .get((left, right))
            .orElse(leafEqMap.get((left, right)))
            .map(_.asInstanceOf[proof.Fact])
            .getOrElse(
              throw new IllegalArgumentException(
                s"injectivityCaseShape: missing equality proof for binder pair (${left}, ${right}). \n ${topEqMap.keys} \n ${leafEqMap.keys}"
              )
            )
        }

      def guardType(guard: BranchGuard): Ty =
        val t = pp.semanticConstructor.semanticSignature2(guard.position)._2
          .substitute(pp.typeSubstitutions*).asInstanceOf[Expr[Ind]]
        ADT.unapply(t).get

      have((bp1 /\ bp2) ==> simplify(A <=> seqEqV)) subproof {
        assume(bp1); assume(bp2)
        val typed1 = have(pp.typingFormulaAt(v1)) by Tautology
        val typed2 = have(pp.typingFormulaAt(v2)) by Tautology

        val fwd = have(A ==> seqEqV) subproof {
          assume(A)
          // top constructor injectivity at the (identity) top variables
          instAll(topInjThm, top1.map(x => x: Expr[Ind]) ++ top2.map(x => x: Expr[Ind]))
          val topInj = lastStep
          val topEq = have(seqEq(top1, top2)) by Tautology.from(topInj, typed1, typed2)
          val leafEqMap = guards1.zip(guards2).foldLeft(Map.empty[(Variable[Ind], Variable[Ind]), lisa.SetTheoryLibrary.Proof#Fact]) {
            case (acc, (guard1, guard2)) =>
              require(
                guard1.position == guard2.position,
                s"injectivityCaseShape: guard positions do not align (${guard1.position} vs ${guard2.position})."
              )
              // guard terms equal:  g(inner1) = guard1.binder = guard2.binder = g(inner2)
              val gb = have(guard1.binder === guard2.binder) by Tautology.from(topEq)
              val g1 = have(guard1.binder === guard1.guardTerm) by Tautology
              val g2 = have(guard2.binder === guard2.guardTerm) by Tautology
              val g1r = have(guard1.guardTerm === guard1.binder) by Congruence.from(g1)
              val g1b2 = have(guard1.guardTerm === guard2.binder) by Tautology.from(
                altEqualityTransitivity of (x := guard1.guardTerm, y := guard1.binder, z := guard2.binder), g1r, gb)
              val guardEq = have(guard1.guardTerm === guard2.guardTerm) by Tautology.from(
                altEqualityTransitivity of (x := guard1.guardTerm, y := guard2.binder, z := guard2.guardTerm), g1b2, g2)
              acc ++ injectEq(
                parse(guard1.guardTerm),
                parse(guard2.guardTerm),
                guardType(guard1),
                guardEq.asInstanceOf[lisa.SetTheoryLibrary.Proof#Fact]
              )
          }
          val topEqMap = topBinderEqualities(topEq.asInstanceOf[lisa.SetTheoryLibrary.Proof#Fact])
          val componentEqs = orderedBinderEqualities(topEqMap, leafEqMap)
          have(seqEqV) by Tautology.from(componentEqs*)
        }
        val bwd = have(seqEqV ==> A) subproof {
          assume(seqEqV)
          val topEqs = top1.zip(top2).map((a, b) => have((a: Expr[Ind]) === (b: Expr[Ind])) by Tautology)
          have(A) by Congruence.from(topEqs*)
        }
        have(simplify(A <=> seqEqV)) by Tautology.from(fwd, bwd)
      }
      for vv <- (v1 ++ v2).reverse do
        thenHave(∀(vv, lastStep.statement.right.head)) by RightForall
      have(thesis) by Tautology.from(lastStep)
    }
}
