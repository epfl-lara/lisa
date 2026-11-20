package lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Integer.nonZeroOmegaHasPredecessor
import lisa.maths.SetTheory.Ordinals.Integer.subsetSuccessor
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.PatternMatching.PatternNode
import lisa.maths.SetTheory.Types.ADT.PatternMatching.PatternNode.Bind
import lisa.maths.SetTheory.Types.ADT.PatternMatching.PatternNode.Construct
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.DecisionTree.Leaf
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.DecisionTree.Occurrence
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.DecisionTree.Split
import lisa.maths.SetTheory.Types.ADT.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADT.interface.ADT
import lisa.maths.SetTheory.Types.ADT.interface.Constructor
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.instantiate
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.ADT.support.proofs.PropositionalFacts.altEqualityTransitivity
import lisa.maths.SetTheory.Types.ADT.syntax.AST._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.BasicStep.LeftExists
import lisa.utils.prooflib.BasicStep.LeftOr
import lisa.utils.prooflib.BasicStep.Restate
import lisa.utils.prooflib.BasicStep.RightExists
import lisa.utils.prooflib.BasicStep.RightForall
import lisa.utils.prooflib.InstantiateForall
import lisa.utils.prooflib.InstantiateForallSeq
import lisa.utils.prooflib.QuantifiersIntro
import lisa.utils.prooflib.Thm

/**
 * Coverage, branch selection, and incompatibility proofs using resolved patterns.
 */
private[ADT] object PatternProofs {

  /**
   * The type of a pattern node, including opaque types at variable leaves.
   */
  type Ty = Expr[Ind]

  private def childTypes(c: Constructor[?], targs: Seq[Expr[Ind]]): Seq[Ty] =
    val subst = c.semantic.typeVariablesSeq.zip(targs).map((v, a) => v := a)
    c.semantic.semanticSignature2.map { case (_, tyTerm) =>
      tyTerm.substitute(subst*)
    }

  private def renderCase(pp: Pattern): String =
    DecisionTree.showPattern(pp.resolved)

  private def instantiatePrefix(formula: Expr[Prop], args: Seq[Expr[Ind]]): Expr[Prop] =
    args.foldLeft(formula) { (current, arg) =>
      current match
        case forall(qv, phi) => phi.substitute(qv := arg)
        case _ => current
    }

  private def instAll(thm: Theorem, terms: Seq[Expr[Ind]])(using proof: lisa.SetTheoryLibrary.Proof): Unit =
    val source = have(thm.statement.right.head) by Tautology.from(thm)
    val instantiated = instantiatePrefix(source.statement.right.head, terms)
    have(instantiated) by InstantiateForallSeq(terms)(source)

  /**
   * Proves typing of a resolved pattern from its binder typings.
   */
  private def typing(using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      pattern: PatternNode,
      premises: Seq[Thm] = Seq.empty
  ): Thm =
    val goal = pattern.term :: pattern.typ
    pattern match
      case Bind(_, _) => have(goal) by Tautology.from(premises*)
      case Construct(constructor, typeArgs, arguments) =>
        val argumentFacts = arguments.map(argument => typing(argument, premises))
        val substitutions =
          constructor.typeVariablesSeq.zip(typeArgs).map((v, term) => v := term) ++
            constructor.semantic.variables.zip(arguments.map(_.term)).map((v, term) => v := term)
        val introduction: Thm =
          if substitutions.isEmpty then constructor.introApp else constructor.introApp.of(substitutions*)
        have(goal) by Tautology.from((introduction +: argumentFacts)*)

  private def renderAlignedGuards(
      p1: Pattern,
      p2: Pattern
  ): String =
    val byPos1 = p1.guards.map(g => g.position -> g.pattern).toMap
    val byPos2 = p2.guards.map(g => g.position -> g.pattern).toMap
    val sharedPositions = byPos1.keySet.intersect(byPos2.keySet).toSeq.sorted
    if sharedPositions.isEmpty then "none"
    else
      sharedPositions
        .map { pos =>
          val left = DecisionTree.showPattern(byPos1(pos))
          val right = DecisionTree.showPattern(byPos2(pos))
          s"arg $pos: $left vs $right"
        }
        .mkString("; ")

  def divergePath(p: PatternNode, q: PatternNode): Option[List[Int]] = (p, q) match
    case (Construct(c, _, _), Construct(d, _, _)) if c.id != d.id => Some(Nil)
    case (Construct(_, _, as), Construct(_, _, bs)) =>
      as.lazyZip(bs)
        .zipWithIndex
        .iterator
        .map { case ((a, b), i) => divergePath(a, b).map(i :: _) }
        .collectFirst { case Some(path) => path }
    case _ => None

  // The disjointness theorem for two constructors of the same ADT. Only needed to
  // capture the ADT's arity so the two constructors line up. Like `injectivity`, the
  // result is closed over the ADT's type variables, so callers instantiate it by
  // passing the type arguments ahead of the constructor arguments.
  private def crossInj(adt: ADT[?], c: Constructor[?], d: Constructor[?]): Theorem =
    adt match
      case a: ADT[n] =>
        a.disjointness(c.asInstanceOf[Constructor[n]], d.asInstanceOf[Constructor[n]])

  // The top constructor's injectivity for a pattern, specialized to its type args.
  // (Used directly so it is unaffected by a pattern's overridden `injectivity`.)
  def constructorInjectivity(pp: Pattern): Theorem =
    val base = pp.semanticConstructor.injectivity
    if pp.typeSubstitutions.isEmpty then base
    else
      Lemma.generated(base.statement.substitute(pp.typeSubstitutions*)) {
        have(thesis) by Restate.from(base.of(pp.typeSubstitutions*))
      }

  // ════════════════════════════════════════════════════════════════════════
  //  Disjointness:  binderTypings |- ¬(pattern_i === pattern_j)
  // ════════════════════════════════════════════════════════════════════════
  // TODO:??? factorize with injectEq (see also incompatibleProof)
  def incompatibleProof(p: PatternNode, q: PatternNode): Theorem =
    val path = divergePath(p, q).getOrElse(
      throw new IllegalArgumentException("incompatibleProof: patterns are compatible (overlap).")
    )
    val tp = p.term
    val tq = q.term
    val typedHyps = wellTypedSet(p.typingSignature ++ q.typingSignature).toSeq

    Lemma.generated((typedHyps |- !(tp === tq))) { sp ?=>
      typedHyps.foreach(h => assume(h))

      def typings(args: List[PatternNode]): Seq[Thm] = args.map(typing(_))

      // Leaves `¬(termOf(p) === termOf(q))` as the latest fact.
      def disprove(p: PatternNode, q: PatternNode, path: List[Int]): Unit =
        val tpc = p.term; val tqc = q.term
        (p, q) match
          case (Construct(c, targs, as), Construct(d, _, bs)) if path.isEmpty =>
            // cross-constructor injectivity:  typed ⇒ ¬(c(..) === d(..))
            instAll(crossInj(c.adt, c, d), targs ++ as.map(_.term) ++ bs.map(_.term))
            val injInst = lastStep
            val argTypings = typings(as) ++ typings(bs)
            have(!(tpc === tqc)) by Tautology.from((injInst +: argTypings)*)
          case (Construct(c, targs, as), Construct(_, _, bs)) =>
            val i = path.head
            disprove(as(i), bs(i), path.tail)
            val argDiseq = lastStep
            // same-head injectivity:  typed ⇒ ((c(as) === c(bs)) <=> (as === bs))
            instAll(c.injectivity, targs ++ as.map(_.term) ++ bs.map(_.term))
            val injInst = lastStep
            val argTypings = typings(as) ++ typings(bs)
            have(!(tpc === tqc)) by Tautology.from((injInst +: argDiseq +: argTypings)*)
          case _ => throw new IllegalArgumentException("disprove: malformed path.")

      disprove(p, q, path)
      have(thesis) by Tautology.from(lastStep)
    }

  private def proveByCongruence(using proof: lisa.SetTheoryLibrary.Proof)(formula: Expr[Prop], eqFacts: List[Thm]): Thm =
    formula match
      case lhs /\ rhs =>
        val leftFact = proveByCongruence(lhs, eqFacts)
        val rightFact = proveByCongruence(rhs, eqFacts)
        have(formula) by RightAnd(leftFact, rightFact)
      case _ =>
        have(formula) by Congruence.from(eqFacts*)

  private def finishCoverLeaf(
      variables: Seq[Variable[Ind]],
      witnesses: Seq[Expr[Ind]],
      body: Expr[Prop],
      condition: Expr[Prop],
      inputEquality: Expr[Prop],
      equalities: List[Expr[Prop]],
      goal: Expr[Prop]
  )(using proof: lisa.SetTheoryLibrary.Proof): Unit =
    val substitutions = variables.zip(witnesses).map((v, term) => v := term)
    val equalityFacts = equalities.map(eq => have(eq) by Restate)
    val guardFact = proveByCongruence(condition.substitute(substitutions*), equalityFacts)
    val inputFact = have(inputEquality.substitute(substitutions*)) by Congruence.from(equalityFacts*)
    have(body.substitute(substitutions*)) by Tautology.from(guardFact, inputFact)
    for i <- variables.indices.reverse do
      val quantified = existsSeq(
        variables.drop(i),
        body.substitute(variables.take(i).zip(witnesses.take(i)).map((v, term) => v := term)*)
      )
      thenHave(quantified) by RightExists
    have(goal) by Tautology.from(lastStep)

  // Occurrence values and equality formulas survive descent; proof facts stay in their local subproof.
  private def coverTree(
      tree: DecisionTree,
      values: Map[Occurrence, Expr[Ind]],
      equalities: List[Expr[Prop]],
      goal: Expr[Prop],
      avoid: Seq[Expr[?]]
  )(
      leaf: (Leaf, Map[Occurrence, Expr[Ind]], List[Expr[Prop]]) => lisa.SetTheoryLibrary.Proof ?=> Unit
  )(using proof: lisa.SetTheoryLibrary.Proof): Unit = tree match
    case selected: Leaf => leaf(selected, values, equalities)
    case Split(occurrence, domain, branches) =>
      val value = values(occurrence)
      val forbidden = avoid ++ proof.assumptions ++ values.values ++ Seq(goal, domain.term)
      val cases = branches.map { (constructor, subtree) =>
        val arguments = (0 until constructor.semantic.arity).foldLeft(Vector.empty[Variable[Ind]]) { (args, i) =>
          args :+ Variable[Ind](freshId(forbidden ++ args, s"caseArg$i"))
        }
        val equation = value === appSeq(constructor.semantic.term(domain.typeArgs))(arguments)
        val premise = wellTypedFormula(arguments.zip(childTypes(constructor, domain.typeArgs))) /\ equation
        val childValues = values ++ arguments.zipWithIndex.map((arg, i) => (occurrence :+ i) -> arg)
        val branch = have(premise |- goal) subproof {
          assume(premise)
          coverTree(subtree, childValues, equalities :+ equation, goal, avoid)(leaf)
        }
        val quantified = existsSeq(arguments, premise)
        val fact = have(quantified |- goal) by QuantifiersIntro(arguments)(branch)
        (quantified, fact)
      }
      val disjunction = seqOr(cases.map(_._1))
      val elimination: Thm = if domain.typeArgs.isEmpty then domain.base.elim else domain.base.elim.of(domain.typeArgs*)
      val instantiated = have(value :: domain.term ==> disjunction) by InstantiateForall(value)(elimination)
      val exhaustive = have(disjunction) by Tautology.from(instantiated)
      if cases.isEmpty then have(goal) by Tautology.from(exhaustive)
      else
        val combined =
          if cases.size == 1 then have(disjunction |- goal) by Restate.from(cases.head._2)
          else have(disjunction |- goal) by LeftOr((cases.map(_._2)).map(_.kernel))
        have(goal) by Tautology.from(exhaustive, combined)

  private def rootSplit(tree: DecisionTree): Split = tree match
    case root: Split if root.occurrence.isEmpty => root
    case _ => throw new IllegalArgumentException("A compiled pattern system must split its input at the root.")

  private def patternVariables(patterns: Seq[Pattern]): Seq[Expr[?]] =
    patterns.flatMap(p => p.binders ++ p.variables2 ++ Seq(p.resolved.term, p.specializedAdtTerm))

  private def innerWitnesses(
      pattern: Pattern,
      leaf: Leaf,
      values: Map[Occurrence, Expr[Ind]]
  ): Seq[Expr[Ind]] =
    val positions = leaf.bindings.toMap
    pattern.binders.drop(pattern.arity).map(v => values(positions(v)))

  /**
   * Proves whole-domain coverage by traversing the retained tree.
   */
  def coverageCaseShape(tree: DecisionTree, patterns: Seq[Pattern]): Theorem =
    val root = rootSplit(tree)
    val avoid = patternVariables(patterns) :+ root.domain.term
    val input = Variable[Ind](freshId(avoid, "scrutX"))
    val disjuncts = patterns.map(p => existsSeq(p.variables2, p.freshBranchPremise /\ (input === p.freshInputTerm)))
    val goal = simplify(seqOr(disjuncts))
    Lemma.generated(∀(input :: root.domain.term, goal)) {
      have(input :: root.domain.term ==> goal) subproof {
        assume(input :: root.domain.term)
        coverTree(root, Map(Nil -> input), Nil, goal, avoid) { (leaf, values, equalities) =>
          val pattern = patterns(leaf.clauseIndex)
          val witnesses = (0 until pattern.arity).map(i => values(List(i))) ++ innerWitnesses(pattern, leaf, values)
          val equation = input === pattern.freshInputTerm
          finishCoverLeaf(pattern.variables2, witnesses, pattern.freshBranchPremise /\ equation, pattern.freshBranchCondition, equation, equalities, goal)
        }
      }
      thenHave(thesis) by RightForall
    }

  /**
   * Proves branch selection from the retained subtree of the known outer constructor.
   */
  def branchSelectionForCaseShape(
      tree: DecisionTree,
      constructor: SemanticConstructor,
      term: Expr[Ind],
      patterns: Seq[Pattern]
  ): Theorem =
    val root = rootSplit(tree)
    val (head, subtree) = root.branches
      .find(_._1.semantic == constructor)
      .getOrElse(
        throw new IllegalArgumentException(s"Constructor ${constructor.name} does not belong to this pattern system.")
      )
    val selected = patterns.filter(_.semanticConstructor == constructor)
    val top = selected.head.variables2.take(constructor.arity)
    val typing = wellTypedFormula(top.zip(childTypes(head, root.domain.typeArgs)))
    val inputEquality = term === appSeq(constructor.term(root.domain.typeArgs))(top)
    val goal = seqOr(selected.map(_.branchSelectionDisjunct(term)))
    val values: Map[Occurrence, Expr[Ind]] = Map(Nil -> term) ++ top.zipWithIndex.map((v, i) => List(i) -> v)
    val avoid = patternVariables(patterns) ++ Seq(term, root.domain.term)
    Lemma.generated(forallSeq(top, (typing /\ inputEquality) ==> goal)) {
      have((typing /\ inputEquality) ==> goal) subproof {
        assume(typing)
        assume(inputEquality)
        coverTree(subtree, values, List(inputEquality), goal, avoid) { (leaf, values, equalities) =>
          val pattern = patterns(leaf.clauseIndex)
          finishCoverLeaf(
            pattern.variables2.drop(pattern.arity),
            innerWitnesses(pattern, leaf, values),
            pattern.branchSelectionBody(term),
            pattern.freshBranchCondition,
            term === pattern.freshInputTerm,
            equalities,
            goal
          )
        }
      }
      have(thesis) by QuantifiersIntro(top)(lastStep)
    }

  // ════════════════════════════════════════════════════════════════════════
  //  Disjointness in the trait shape:
  //    (p1.branchPremise1 ∧ p2.freshBranchPremise) ⟹ ¬(p1.inputTerm1 = p2.inputTerm2)
  //  Same outer structure as the existing nullary `incompatible`; the final
  //  guard-term disequality uses the recursive divergence peel instead.
  // ════════════════════════════════════════════════════════════════════════
  def incompatibleCaseShape(p1: Pattern, p2: Pattern): Theorem =
    incompatibleCaseShapeN(p1, p2)

  private[semantics] def sameHeadGuardEquality(
      p1: Pattern,
      p2: Pattern,
      guard1: BranchGuard,
      guard2: BranchGuard
  ): Theorem =
    Lemma.generated(
      (p1.branchPremise1 /\ p2.freshBranchPremise /\ (p1.inputTerm1 === p2.inputTerm2)) ==>
        (guard1.guardTerm === guard2.guardTerm)
    ) {
      val branch = assume(p1.branchPremise1 /\ p2.freshBranchPremise /\ (p1.inputTerm1 === p2.inputTerm2))
      val branch1Typed = have(p1.branchPremise1) by Tautology.from(branch)
      val branch2Typed = have(p2.freshBranchPremise) by Tautology.from(branch)
      val inputsEqual = have(p1.inputTerm1 === p2.inputTerm2) by Tautology.from(branch)

      val ctorInj = constructorInjectivity(p1)
      val injectivitySchema = have(ctorInj.statement.right.head) by Tautology.from(ctorInj)
      val arguments = p1.variables1.take(p1.arity) ++ p2.variables2.take(p2.arity)
      val injectivityAtVars = have(instantiatePrefix(injectivitySchema.statement.right.head, arguments)) by
        InstantiateForallSeq(arguments)(injectivitySchema)

      val guardedArgsEqual = have(guard1.binder === guard2.binder) by
        Tautology.from(injectivityAtVars, branch1Typed, branch2Typed, inputsEqual)
      val guard1Eq = have(guard1.binder === guard1.guardTerm) by Tautology.from(branch1Typed)
      val guard2Eq = have(guard2.binder === guard2.guardTerm) by Tautology.from(branch2Typed)
      val guard1EqRev = have(guard1.guardTerm === guard1.binder) by Congruence.from(guard1Eq)
      val guard1ToGuard2Binder =
        have(guard1.guardTerm === guard2.binder) by Tautology.from(
          altEqualityTransitivity of (x := guard1.guardTerm, y := guard1.binder, z := guard2.binder),
          guard1EqRev,
          guardedArgsEqual
        )
      have(thesis) by Tautology.from(
        altEqualityTransitivity of (x := guard1.guardTerm, y := guard2.binder, z := guard2.guardTerm),
        guard1ToGuard2Binder,
        guard2Eq
      )
    }

  private def incompatibleCaseShapeN(
      p1: Pattern,
      p2: Pattern
  ): Theorem =
    if p1.semanticConstructor != p2.semanticConstructor then
    // different top constructors — `¬(c1(top1) = c2(top2))` from cross injectivity.
    {
      val adt = p1.resolved.constructor.adt
      val targs = p1.resolved.typeArguments
      val c1 = p1.resolved.constructor
      val c2 = p2.resolved.constructor
      val top1 = p1.variables1.take(p1.arity).map(x => x: Expr[Ind])
      val top2 = p2.variables2.take(p2.arity).map(x => x: Expr[Ind])
      Lemma.generated((p1.branchPremise1 /\ p2.freshBranchPremise) ==> !(p1.inputTerm1 === p2.inputTerm2)) {
        val branch = assume(p1.branchPremise1 /\ p2.freshBranchPremise)
        val b1 = have(p1.branchPremise1) by Tautology.from(branch)
        val b2 = have(p2.freshBranchPremise) by Tautology.from(branch)
        val inj = crossInj(adt, c1, c2)
        val fact0 = have(inj.statement.right.head) by Tautology.from(inj)
        val instArgs = targs ++ top1 ++ top2
        val target = instantiatePrefix(fact0.statement.right.head, instArgs)
        val fact = have(target) by InstantiateForallSeq(instArgs)(fact0)
        have(!(p1.inputTerm1 === p2.inputTerm2)) by Tautology.from(fact, b1, b2)
      }
    } else
      val guards1 = p1.guardsAt(p1.variables1)
      val guards2 = p2.freshGuards.map(guard => guard.position -> guard).toMap
      val selectedGuards = guards1.iterator
        .flatMap(guard => guards2.get(guard.position).map(guard -> _))
        .collectFirst {
          case (guard1, guard2) if divergePath(guard1.pattern, guard2.pattern).nonEmpty =>
            (guard1, guard2)
        }
        .getOrElse(
          throw new IllegalArgumentException(
            s"""incompatibleCaseShape rejected two overlapping nested cases for constructor ${p1.semanticConstructor.name}.
               |case 1: ${renderCase(p1)}
               |case 2: ${renderCase(p2)}
               |No divergent aligned guard pair was found, so the two cases still overlap.
               |Aligned guarded positions: ${renderAlignedGuards(p1, p2)}
               |""".stripMargin
          )
        )
      val (guard1, guard2) = selectedGuards

      {
        Lemma.generated(
          (p1.branchPremise1 /\ p2.freshBranchPremise) ==> !(p1.inputTerm1 === p2.inputTerm2)
        ) { sp ?=>
          {
            // --- outer structure (mirrors the existing incompatible) ---
            val branch = assume(p1.branchPremise1 /\ p2.freshBranchPremise)
            assume(p1.inputTerm1 === p2.inputTerm2)
            val inputsEqual = have(p1.inputTerm1 === p2.inputTerm2) by Hypothesis

            val commonEquality = sameHeadGuardEquality(p1, p2, guard1, guard2)
            val guardTermsEqual = have(guard1.guardTerm === guard2.guardTerm) by Tautology.from(commonEquality, branch, inputsEqual)

            // the new part: guard terms are distinct by the recursive peel
            val rp1 = guard1.pattern; val rp2 = guard2.pattern
            val guardDisequalityKernel = incompatibleProof(rp1, rp2)
            val guardTypingFacts =
              wellTypedSet(rp1.typingSignature ++ rp2.typingSignature).toSeq.map(h => have(h) by Tautology.from(branch))
            val guardDisequality = have(!(guard1.guardTerm === guard2.guardTerm)) by
              Tautology.from((guardDisequalityKernel +: guardTypingFacts)*)

            have(thesis) by Tautology.from(guardTermsEqual, guardDisequality)
          }
        }
      }

  // ════════════════════════════════════════════════════════════════════════
  //  Pattern-level injectivity (well-definedness), the shape `samePatternBody
  //  Equality` consumes:
  //    ∀(v1 ++ v2). (branchPremise(v1) ∧ branchPremise(v2))
  //                  ⟹ ((inputTerm(v1) = inputTerm(v2)) ⇔ (v1 === v2))
  //  Forward direction uses the top constructor injectivity plus a recursive
  //  injective descent through the guard term (the mirror of `disprove`).
  // ════════════════════════════════════════════════════════════════════════
  def injectivityCaseShape(pp: Pattern): Theorem =
    val v1 = pp.variables1.toList; val v2 = pp.variables2.toList
    val ar = pp.arity
    val (top1, _) = v1.splitAt(ar); val (top2, _) = v2.splitAt(ar)
    val A = pp.inputTermAt(v1) === pp.inputTermAt(v2)
    val seqEqV = seqEq(v1, v2)
    val bp1 = pp.branchPremiseAt(v1); val bp2 = pp.branchPremiseAt(v2)
    val guards1 = pp.guardsAt(pp.variables1)
    val guards2 = pp.freshGuards
    val topInjThm: Theorem = constructorInjectivity(pp)

    Lemma.generated(forallSeq(v1 ++ v2, (bp1 /\ bp2) ==> simplify(A <=> seqEqV))) {
      // From `termOf(rp1) = termOf(rp2)` derive the leaf (inner-binder) equalities,
      // indexed by the exact binder pair they justify.
      def injectEq(using
          proof: lisa.SetTheoryLibrary.Proof
      )(
          rp1: PatternNode,
          rp2: PatternNode,
          eqFact: Thm
      ): Map[(Variable[Ind], Variable[Ind]), Thm] =
        (rp1, rp2) match
          case (Bind(vl, _), Bind(vr, _)) => Map((vl, vr) -> eqFact)
          case (Construct(c, targs, as1), Construct(_, _, as2)) =>
            val t1 = as1.map(_.term)
            val t2 = as2.map(_.term)
            instAll(c.injectivity, targs ++ t1 ++ t2)
            val injInst = lastStep
            val tys = as1.map(typing(_)) ++ as2.map(typing(_))
            as1.indices.toList.foldLeft(Map.empty[(Variable[Ind], Variable[Ind]), Thm]) { (acc, i) =>
              val argEq = have(t1(i) === t2(i)) by Tautology.from((injInst +: eqFact +: tys)*)
              acc ++ injectEq(as1(i), as2(i), argEq)
            }
          case _ => throw new IllegalArgumentException("injectEq: mismatched guard structure.")

      def topBinderEqualities(using proof: lisa.SetTheoryLibrary.Proof)(topEq: Thm): Map[(Variable[Ind], Variable[Ind]), Thm] =
        top1
          .zip(top2)
          .map { (left, right) =>
            val eqFact: Thm = have((left: Expr[Ind]) === (right: Expr[Ind])) by Tautology.from(topEq)
            (left, right) -> eqFact
          }
          .toMap

      def orderedBinderEqualities(using
          proof: lisa.SetTheoryLibrary.Proof
      )(
          topEqMap: Map[(Variable[Ind], Variable[Ind]), Thm],
          leafEqMap: Map[(Variable[Ind], Variable[Ind]), Thm]
      ): Seq[Thm] =
        v1.zip(v2).map { (left, right) =>
          topEqMap
            .get((left, right))
            .orElse(leafEqMap.get((left, right)))
            .getOrElse(
              throw new IllegalArgumentException(
                s"injectivityCaseShape: missing equality proof for binder pair (${left}, ${right}). \n ${topEqMap.keys} \n ${leafEqMap.keys}"
              )
            )
        }

      have((bp1 /\ bp2) ==> simplify(A <=> seqEqV)) subproof {
        assume(bp1); assume(bp2)
        val typed1 = have(pp.typingFormulaAt(v1)) by Tautology
        val typed2 = have(pp.typingFormulaAt(v2)) by Tautology

        val fwd = have(A ==> seqEqV) subproof { branchProof ?=>
          assume(A)
          // top constructor injectivity at the (identity) top variables
          instAll(topInjThm, top1.map(x => x: Expr[Ind]) ++ top2.map(x => x: Expr[Ind]))
          val topInj = lastStep
          val topEq = have(seqEq(top1, top2)) by Tautology.from(topInj, typed1, typed2)
          val leafEqMap = guards1.zip(guards2).foldLeft(Map.empty[(Variable[Ind], Variable[Ind]), Thm]) { case (acc, (guard1, guard2)) =>
            require(
              guard1.position == guard2.position,
              s"injectivityCaseShape: guard positions do not align (${guard1.position} vs ${guard2.position})."
            )
            // guard terms equal:  g(inner1) = guard1.binder = guard2.binder = g(inner2)
            val gb = have(guard1.binder === guard2.binder) by Tautology.from(topEq)
            val g1 = have(guard1.binder === guard1.guardTerm) by Tautology
            val g2 = have(guard2.binder === guard2.guardTerm) by Tautology
            val g1r = have(guard1.guardTerm === guard1.binder) by Congruence.from(g1)
            val g1b2 = have(guard1.guardTerm === guard2.binder) by Tautology.from(altEqualityTransitivity of (x := guard1.guardTerm, y := guard1.binder, z := guard2.binder), g1r, gb)
            val guardEq = have(guard1.guardTerm === guard2.guardTerm) by Tautology.from(altEqualityTransitivity of (x := guard1.guardTerm, y := guard2.binder, z := guard2.guardTerm), g1b2, g2)
            acc ++ injectEq(
              guard1.pattern,
              guard2.pattern,
              guardEq
            )
          }
          val topEqMap = topBinderEqualities(topEq)
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
      have(thesis) by QuantifiersIntro(v1 ++ v2)(lastStep)
    }

  /**
   * Instantiates typing of a resolved root constructor at supplied value arguments.
   */
  def inputTyping(pattern: Pattern, variables: Seq[Variable[Ind]])(using proof: lisa.SetTheoryLibrary.Proof): Thm =
    require(variables.size == pattern.arity, "Constructor typing requires one value per argument.")
    val substitutions = pattern.typeSubstitutions ++ pattern.semanticConstructor.variables.zip(variables).map((from, to) => from := to)
    instantiate(pattern.resolved.constructor.introApp, substitutions)

  /**
   * Follows a validated recursive field path to prove the target's height bound.
   */
  def descendToBinder(using
      proof: lisa.SetTheoryLibrary.Proof,
      line: sourcecode.Line,
      file: sourcecode.File
  )(
      heightFun: Expr[Ind],
      hValid: Thm,
      currentIndex: Expr[Ind],
      currentIndexInN: Thm,
      leafTyping: Thm,
      currentPat: PatternNode,
      path: List[Int],
      currentInHeight: Thm,
      target: Variable[Ind]
  ): Thm =
    currentPat match
      case Bind(v, _) =>
        if path.nonEmpty || v != target then throw new IllegalArgumentException(s"Asked to descend to $target but reached unrelated binder $v.")
        currentInHeight

      case Construct(c, targs, args) =>
        require(path.nonEmpty && c.semantic.syntacticSignature(path.head)._2 == SelfRef, "Height descent must follow recursive constructor fields.")
        val currentAdt = c.adt
        val predVar = Variable[Ind](freshId(proof.assumptions ++ Seq(currentIndex, target, heightFun, currentPat.term, currentPat.typ), "predVar"))
        val currentTerm = currentPat.term
        val levelSubsts = currentAdt.semantic.typeVariablesSeq.zip(targs).map((v, a) => v := a)
        val currentInZero = {
          have(!(currentTerm ∈ app(heightFun)(∅))) by Tautology.from(
            hValid,
            currentAdt.semantic.height.zeroAt(levelSubsts, Seq(h := heightFun, x := currentTerm))
          )
        }

        val currentIndexNonZero = have(currentIndex =/= ∅) subproof {
          val currentIsZero = assume(currentIndex === ∅)
          have(thesis) by Congruence.from(currentInHeight, currentInZero, currentIsZero)
        }

        val predecessorTheoremAtIndex = have(
          (currentIndex ∈ N, currentIndex =/= ∅) |- ∃(predVar, predVar ∈ N /\ (currentIndex === S(predVar)))
        ) by Tautology.from(
          nonZeroOmegaHasPredecessor.of(α := currentIndex, β := predVar)
        )
        have(currentIndex =/= ∅ |- ∃(predVar, predVar ∈ N /\ (currentIndex === S(predVar)))) subproof {
          assume(currentIndex =/= ∅)
          have(thesis) by Tautology.from(currentIndexInN, predecessorTheoremAtIndex)
        }
        val predWitnessAtIndex = have(∃(predVar, predVar ∈ N /\ (currentIndex === S(predVar)))) by Cut(
          currentIndexNonZero,
          lastStep
        )

        have(
          (predVar ∈ N /\ (currentIndex === S(predVar))) |- target ∈ app(heightFun)(currentIndex)
        ) subproof {
          assume(predVar ∈ N /\ (currentIndex === S(predVar)))
          val currentEqSucc = have(currentIndex === S(predVar)) by Tautology
          val predInN = have(predVar ∈ N) by Tautology

          val currentInSuccPred = have(currentTerm ∈ app(heightFun)(S(predVar))) by Congruence.from(
            currentInHeight,
            currentEqSucc
          )

          val argTerms: Seq[Expr[Ind]] = args.map(_.term)
          val argTypings = args.map(argument => typing(argument, Seq(leafTyping)))
          val semanticSubsts = c.semantic.typeVariablesSeq.zip(targs).map((v, a) => v := a)
          val semanticSigAtArgs =
            argTerms.zip(c.semantic.semanticSignature2.map(_._2.substitute(semanticSubsts*).asInstanceOf[Expr[Ind]]))
          val argsTypedSemantic = { have(wellTypedFormula(semanticSigAtArgs)) by Tautology.from(argTypings*) }
          val heightSigAtArgs = argTerms.zip(c.semantic.syntacticSignature).map {
            case (term, (_, SelfRef)) => term -> app(heightFun)(predVar)
            case (term, (_, TypeArg(name))) => term -> typeExprToTerm(name).substitute(semanticSubsts*).asInstanceOf[Expr[Ind]]
          }
          val recursiveAtPred = c.semantic.recursiveArgInHeightAt(semanticSubsts, argTerms)(heightFun, predVar)
          val childTypingsAtPred = {
            have(wellTypedFormula(heightSigAtArgs)) by Tautology.from(
              hValid,
              predInN,
              argsTypedSemantic,
              currentInSuccPred,
              recursiveAtPred
            )
          }

          val childIdx = path.head
          val childTerm = argTerms(childIdx)
          val childInPred = have(childTerm ∈ app(heightFun)(predVar)) by Tautology.from(childTypingsAtPred)
          val innerAtPred = descendToBinder(
            heightFun = heightFun,
            hValid = hValid,
            currentIndex = predVar,
            currentIndexInN = predInN,
            leafTyping = leafTyping,
            currentPat = args(childIdx),
            path = path.tail,
            currentInHeight = childInPred,
            target = target
          )

          val predSubSucc = have(predVar ⊆ S(predVar)) by Tautology.from(subsetSuccessor.of(n := predVar))
          val predSubCurrent = have(predVar ⊆ currentIndex) by Congruence.from(predSubSucc, currentEqSucc)
          {
            have(target ∈ app(heightFun)(currentIndex)) by Tautology.from(
              hValid,
              currentIndexInN,
              predInN,
              predSubCurrent,
              innerAtPred,
              currentAdt.semantic.height.membershipMonotonicAt(levelSubsts, Seq(h := heightFun, n := currentIndex, m := predVar, x := target))
            )
          }
        }
        val fromPredWitness = thenHave(
          ∃(predVar, predVar ∈ N /\ (currentIndex === S(predVar))) |- target ∈ app(heightFun)(currentIndex)
        ) by LeftExists
        have(target ∈ app(heightFun)(currentIndex)) by Cut(predWitnessAtIndex, fromPredWitness)
}
