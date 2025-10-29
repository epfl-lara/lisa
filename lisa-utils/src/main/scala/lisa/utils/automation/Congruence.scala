package lisa.automation
import leo.datastructures.TPTP.AnnotatedFormula.FormulaType
import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.ProofTacticLib._
import lisa.utils.prooflib.SimpleDeducedSteps._
import lisa.utils.prooflib._

/**
 * This tactic tries to prove a sequent by congruence.
 * Consider the congruence closure of all terms and formulas in the sequent, with respect to all === and <=> left of the sequent.
 * The sequent is provable by congruence if one of the following conditions is met:
 *    - The right side contains an equality s === t or equivalence a <=> b provable in the congruence closure.
 *    - The left side contains an negated equality !(s === t) or equivalence !(a <=> b) provable in the congruence closure.
 *    - There is a formula a on the left and b on the right such that a and b are congruent.
 *    - There are two formulas a and !b on the left such that a and b are congruent.
 *    - There are two formulas a and !b on the right such that a and b are congruent.
 *    - The sequent is Ol-valid without equality reasoning
 * Note that complete congruence closure modulo OL is an open problem.
 *
 * The tactic uses an egraph datastructure to compute the congruence closure.
 * The egraph itselfs relies on two underlying union-find datastructure, one for terms and one for formulas.
 * The union-finds are equiped with an `explain` method that produces a path between any two elements in the same equivalence class.
 * Each edge of the path can come from an external equality, or be the consequence of congruence.
 * The tactic uses uses this path to produce needed proofs.
 */
object Congruence extends ProofTactic with ProofSequentTactic with ProofFactSequentTactic {

  def from(using lib: Library, proof: lib.Proof)(context: proof.Fact*)(bot: Sequent): proof.ProofTacticJudgement =
    val newAssumptions = context.toSet.map(s => (betaReduce(orAllOrFalse(s.statement.right)), s)).filter((f, s) => !bot.left.contains(f))
    val botWithAssumptions = bot.left ++ newAssumptions.map(_._1) |- bot.right
    var seq = botWithAssumptions

    TacticSubproof {
      import lib.*

      have(seq) by this
      for ((assumption, f) <- newAssumptions) {
        seq = (seq.left - assumption) ++ f.statement.left |- seq.right
        have(seq) by Cut(f, lastStep)
      }
    }

  def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
    from(premise)(bot)

  def apply(using lib: Library, proof: lib.Proof)(bot: Sequent): proof.ProofTacticJudgement = TacticSubproof {

    import lib.*

    val egraph = new EGraphExpr()
    egraph.addAll(bot.left)
    egraph.addAll(bot.right)

    bot.left.foreach {
      case l === r => egraph.merge(l, r)
      case l <=> r => egraph.merge(l, r)
      case _ => ()
    }

    if isSameSequent(bot, ⊤) then have(bot) by Restate
    else if bot.left.exists { lf =>
        bot.right.exists { rf =>
          if egraph.idEq(lf, rf) then
            val base = have(bot.left |- (bot.right + lf)) by Restate
            val eq = have(egraph.proveExpr(lf, rf, bot))
            val a = variable[Prop]
            have((bot.left + (lf <=> rf)) |- (bot.right)) by RightSubstEq.withParameters(Seq((lf, rf)), (Seq(a), a))(base)
            have(bot) by Cut(eq, lastStep)
            true
          else false
        } ||
        bot.left.exists {
          case rf2 @ ¬(rf) if egraph.idEq(lf, rf) =>
            val base = have((bot.left + !lf) |- bot.right) by Restate
            val eq = have(egraph.proveExpr(lf, rf.asInstanceOf, bot))
            val a = variable[Prop]
            have((bot.left + makeEq(lf, rf)) |- (bot.right)) by LeftSubstEq.withParameters(Seq((lf, rf)), (Seq(a), !a))(base)
            have(bot) by Cut(eq, lastStep)
            true
          case _ => false
        } || {
          lf match
            case ¬(a === b) if egraph.idEq(a, b) =>
              have(egraph.proveExpr(a, b, bot))
              true
            case ¬(a <=> b) if egraph.idEq(a, b) =>
              have(egraph.proveExpr(a, b, bot))
              true
            case _ => false
        }

      }
    then ()
    else if bot.right.exists { rf =>
        bot.right.exists {
          case lf2 @ ¬(lf) if egraph.idEq(lf, rf) =>
            val base = have((bot.left) |- (bot.right + !rf)) by Restate
            val eq = have(egraph.proveExpr[Prop](lf.asInstanceOf, rf, bot))
            val a = variable[Prop]
            have((bot.left + makeEq(lf, rf)) |- (bot.right)) by RightSubstEq.withParameters(Seq((lf, rf)), (Seq(a), !a))(base)
            have(bot) by Cut(eq, lastStep)
            true
          case _ => false
        } || {
          rf match
            case a === b if egraph.idEq(a, b) =>
              have(egraph.proveExpr(a, b, bot))
              true
            case a <=> b if egraph.idEq(a, b) =>
              have(egraph.proveExpr(a, b, bot))
              true
            case _ => false
        }
      }
    then ()
    else return proof.InvalidProofTactic(s"No congruence found to show sequent\n $bot")

  }

}

class UnionFind[T] {
  // parent of each element, leading to its root. Uses path compression
  val parent = scala.collection.mutable.Map[T, T]()
  // original parent of each element, leading to its root. Does not use path compression. Used for explain.
  val realParent = scala.collection.mutable.Map[T, (T, ((T, T), Boolean, Int))]()
  // keep track of the rank (i.e. number of elements bellow it) of each element. Necessary to optimize union.
  val rank = scala.collection.mutable.Map[T, Int]()
  // tracks order of ancientness of unions.
  var unionCounter = 0

  /**
   * add a new element to the union-find.
   */
  def add(x: T): Unit = {
    parent(x) = x
    realParent(x) = (x, ((x, x), true, 0))
    rank(x) = 0
  }

  /**
   * @param x the element whose parent we want to find
   * @return the root of x
   */
  def find(x: T): T = {
    var root = x
    while parent(root) != root do root = parent(root)
    var y = x
    while parent(y) != root do
      val p = parent(y)
      parent(y) = root
      y = p
    root
  }

  /**
   * Merges the classes of x and y
   */
  def union(x: T, y: T): Unit = {
    unionCounter += 1
    val xRoot = find(x)
    val yRoot = find(y)
    if (xRoot == yRoot) return
    if (rank(xRoot) < rank(yRoot)) {
      parent(xRoot) = yRoot
      realParent(xRoot) = (yRoot, ((x, y), true, unionCounter))
    } else if (rank(xRoot) > rank(yRoot)) {
      parent(yRoot) = xRoot
      realParent(yRoot) = (xRoot, ((x, y), false, unionCounter))
    } else {
      parent(yRoot) = xRoot
      realParent(yRoot) = (xRoot, ((x, y), false, unionCounter))
      rank(xRoot) = rank(xRoot) + 1
    }
  }

  private def getPathToRoot(x: T): List[T] = {
    if x == find(x) then List(x)
    else
      val next = realParent(x)
      x :: getPathToRoot(next._1)

  }

  private def getExplanationFromTo(x: T, c: T): List[(T, ((T, T), Boolean, Int))] = {
    if x == c then List()
    else
      val next = realParent(x)
      next :: getExplanationFromTo(next._1, c)
  }

  private def lowestCommonAncestor(x: T, y: T): Option[T] = {
    val pathX = getPathToRoot(x)
    val pathY = getPathToRoot(y)
    pathX.find(pathY.contains)
  }

  /**
   * Returns a path from x to y made of pairs of elements (u, v)
   * such that union(u, v) was called.
   */
  def explain(x: T, y: T): Option[List[(T, T)]] = {

    if (x == y) then return Some(List())
    val lca = lowestCommonAncestor(x, y)
    lca match
      case None => None
      case Some(lca) =>
        var max: ((T, T), Boolean, Int) = ((x, x), true, 0)
        var itX = x
        while itX != lca do
          val (next, ((u1, u2), b, c)) = realParent(itX)
          if c > max._3 then max = ((u1, u2), b, c)
          itX = next

        var itY = y
        while itY != lca do
          val (next, ((u1, u2), b, c)) = realParent(itY)
          if c > max._3 then max = ((u1, u2), !b, c)
          itY = next

        val u1 = max._1._1
        val u2 = max._1._2
        if max._2 then Some(explain(x, u1).get ++ List((u1, u2)) ++ explain(u2, y).get)
        else Some(explain(x, u2).get ++ List((u1, u2)) ++ explain(u1, y).get)
  }

  /**
   * Returns the set of all roots of all classes
   */
  def getClasses: Set[T] = parent.keys.map(find).toSet

  /**
   * Add all elements in the collection to the union-find
   */
  def addAll(xs: Iterable[T]): Unit = xs.foreach(add)

}

///////////////////////////////
///////// E-graph /////////////
///////////////////////////////

import scala.collection.mutable

class EGraphExpr() {

  val parents = mutable.Map[Expr[?], mutable.Set[Expr[?]]]()
  val UF = new UnionFind[Expr[?]]()

  def find[T](id: Expr[T]): Expr[T] = UF.find(id).asInstanceOf[Expr[T]]

  trait Step
  case class ExternalStep(between: (Expr[?], Expr[?])) extends Step
  case class CongruenceStep(between: (Expr[?], Expr[?])) extends Step

  val proofMap = mutable.Map[(Expr[?], Expr[?]), Step]()

  def explain(id1: Expr[?], id2: Expr[?]): Option[List[Step]] = {
    val steps = UF.explain(id1, id2)
    steps.map(_.foldLeft((id1, List[Step]())) { case ((prev, acc), step) =>
      proofMap(step) match
        case s @ ExternalStep((l, r)) =>
          if l == prev then (r, s :: acc)
          else if r == prev then (l, ExternalStep(r, l) :: acc)
          else throw new Exception("Invalid proof recovered: It is not a chain")
        case s @ CongruenceStep((l, r)) =>
          if l == prev then (r, s :: acc)
          else if r == prev then (l, CongruenceStep(r, l) :: acc)
          else throw new Exception("Invalid proof recovered: It is not a chain")

    }._2.reverse)
  }

  def makeSingletonEClass(node: Expr[?]): Expr[?] = {
    UF.add(node)
    if !parents.contains(node) then parents(node) = mutable.Set()
    node
  }

  def idEq(id1: Expr[?], id2: Expr[?]): Boolean = find(id1) == find(id2)

  def canonicalize(node: Expr[?]): Expr[?] = node match
    case App(f, a) => App.unsafe(canonicalize(f), find(a))
    case _ => node

  def add(node: Expr[?]): Expr[?] =
    if codes.contains(node) then node
    else codes(node) = codes.size
    makeSingletonEClass(node)
    node match
      case Multiapp(f, args) =>
        args.foreach(child =>
          add(child)
          parents(find(child)).add(node)
        )
    mapSigs(canSig(node)) = node
    node

  def addAll(nodes: Iterable[Expr[Ind] | Expr[Prop]]): Unit =
    nodes.foreach { e =>
      (e: @unchecked) match
        case node: Expr[Ind] if node.sort == K.Ind => add(node)
        case node: Expr[Prop] if node.sort == K.Prop => add(node)
        case _ => ()
    }

  def merge[S](id1: Expr[S], id2: Expr[S]): Unit = {
    mergeWithStep(id1, id2, ExternalStep((id1, id2)))
  }

  def mergeUnsafe(id1: Expr[?], id2: Expr[?]): Unit = {
    mergeWithStep(id1, id2, ExternalStep((id1, id2)))
  }

  type Sig = (Expr[?], List[Int])
  val mapSigs = mutable.Map[Sig, Expr[?]]()
  val codes = mutable.Map[Expr[?], Int]()

  def canSig(node: Expr[?]): Sig = node match
    case Multiapp(label, args) =>
      (label, args.map(a => codes(find(a))).toList)

  protected def mergeWithStep(id1: Expr[?], id2: Expr[?], step: Step): Unit = {
    if id1.sort != id2.sort then throw new IllegalArgumentException("Cannot merge nodes of different sorts")
    if (id1.sort != K.Ind && id1.sort != K.Prop) || (id2.sort != K.Ind && id2.sort != K.Prop) then return ()
    if find(id1) == find(id2) then ()
    else
      proofMap((id1, id2)) = step
      val parents1 = parents(find(id1))
      val parents2 = parents(find(id2))

    if find(id1) == find(id2) then return ()

    proofMap((id1, id2)) = step
    val (small, big) = if parents(find(id1)).size < parents(find(id2)).size then (id1, id2) else (id2, id1)
    codes(find(small)) = codes(find(big))
    UF.union(id1, id2)
    val newId = find(id1)
    var worklist = List[(Expr[?], Expr[?], Step)]()

    parents(small).foreach { pExpr =>
      val canonicalPExpr = canSig(pExpr)
      if mapSigs.contains(canonicalPExpr) then
        val qExpr = mapSigs(canonicalPExpr)

        worklist = (pExpr, qExpr, CongruenceStep((pExpr, qExpr))) :: worklist
      else mapSigs(canonicalPExpr) = pExpr
    }
    parents(newId) = parents(big)
    parents(newId).addAll(parents(small))
    worklist.foreach { case (l, r, step) => mergeWithStep(l, r, step) }
  }

  def proveExpr[S](using lib: Library, proof: lib.Proof)(id1: Expr[S], id2: Expr[S], base: Sequent): proof.ProofTacticJudgement =
    TacticSubproof { proveInnerTerm(id1, id2, base) }

  def proveInnerTerm(using lib: Library, proof: lib.Proof)(id1: Expr[?], id2: Expr[?], base: Sequent): Unit = {
    import lib.*
    val steps = explain(id1, id2)
    steps match {
      case None => throw new Exception("No proof found in the egraph")
      case Some(steps) =>
        if steps.isEmpty then have(base.left |- (base.right + (makeEq(id1, id2)))) by Restate
        steps.foreach {
          case ExternalStep((l, r)) =>
            val goalSequent = base.left |- (base.right + (makeEq(id1, r)))
            if l == id1 then have(goalSequent) by Restate
            else
              val x = variable[Ind](freshId(Seq(id1)))
              have(goalSequent) by RightSubstEq.withParameters(List((l, r)), (Seq(x), makeEq(id1, x)))(lastStep)
          case CongruenceStep((l, r)) =>
            val prev = if id1 != l then lastStep else null
            val leqr = have(base.left |- (base.right + (makeEq(l, r)))) subproof { sp ?=>
              (l, r) match
                case (Multiapp(labell, argsl), Multiapp(labelr, argsr)) if labell == labelr && argsl.size == argsr.size =>
                  var freshn = freshId((l.freeVars ++ r.freeVars).map(_.id), "n").no
                  val ziped = (argsl zip argsr)
                  var zip = List[(Expr[?], Expr[?])]()
                  var children = List[Expr[?]]()
                  var vars = List[Variable[?]]()
                  var steps = List[(Expr[Prop], sp.ProofStep)]()
                  ziped.reverse.foreach { (al, ar) =>
                    if al == ar then children = al :: children
                    else {
                      val x = variable(Identifier("n", freshn), al.sort)
                      freshn = freshn + 1
                      children = x :: children
                      vars = x :: vars
                      steps = (makeEq(al, ar), have(proveExpr(al, ar.asInstanceOf, base))) :: steps
                      zip = (al, ar) :: zip
                    }
                  }
                  have(base.left |- (base.right + makeEq(l, l))) by Restate
                  val eqs = zip.map((l, r) => makeEq(l, r))
                  val goal = have((base.left ++ eqs) |- (base.right + makeEq(l, r))).by.bot
                  have((base.left ++ eqs) |- (base.right + makeEq(l, r))) by RightSubstEq.withParameters(zip, (vars, makeEq(l, Multiapp.unsafe(labelr, children))))(lastStep)
                  steps.foreach { s =>
                    have(
                      if s._2.bot.left.contains(s._1) then lastStep.bot else lastStep.bot -<< s._1
                    ) by Cut(s._2, lastStep)
                  }
                case _ =>
                  println(s"l: $l")
                  println(s"r: $r")
                  throw Exception("Unreachable")

            }
            if id1 != l then
              val goalSequent = base.left |- (base.right + (makeEq(id1, r)))
              val x = variable(freshId(Seq(id1)), id1.sort)
              have(goalSequent +<< makeEq(l, r)) by RightSubstEq.withParameters(List((l, r)), (Seq(x), makeEq(id1, x)))(prev)
              have(goalSequent) by Cut(leqr, lastStep)
        }
    }
  }

  /*

  def proveExpr(using lib: Library, proof: lib.Proof)(id1: Prop, id2:Prop, base: Sequent): proof.ProofTacticJudgement =
    TacticSubproof { proveInnerFormula(id1, id2, base) }

  def proveInnerFormula(using lib: Library, proof: lib.Proof)(id1: Prop, id2:Prop, base: Sequent): Unit = {
    import lib.*
    val steps = explain(id1, id2)
    steps match {
      case None => throw new Exception("No proof found in the egraph")
      case Some(steps) =>
        if steps.isEmpty then have(base.left |- (base.right + (id1 <=> id2))) by Restate
        steps.foreach {
          case ExternalStep((l, r)) =>
            val goalSequent = base.left |- (base.right + (id1 <=> r))
            if l == id1 then
              have(goalSequent) by Restate
            else
              val x = freshVariableFormula(id1)
              have(goalSequent) by RightSubstEq.withParameters(List((l, r)), lambda(x, id1 <=> x))(lastStep)
          case CongruenceStep((l, r)) =>
            val prev = if id1 != l then lastStep else null
            val leqr = have(base.left |- (base.right + (l <=> r))) subproof { sp ?=>
              (l, r) match
                case (AppliedConnector(labell, argsl), AppliedConnector(labelr, argsr)) if labell == labelr && argsl.size == argsr.size =>
                  var freshn = freshId((l.freeVariableFormulas ++ r.freeVariableFormulas).map(_.id), "n").no
                  val ziped = (argsl zip argsr)
                  var zip = List[(Prop, Prop)]()
                  var children = List[Prop]()
                  var vars = List[VariableFormula]()
                  var steps = List[(Prop, sp.ProofStep)]()
                  ziped.reverse.foreach { (al, ar) =>
                    if al == ar then children = al :: children
                    else {
                      val x = VariableFormula(Identifier("n", freshn))
                      freshn = freshn + 1
                      children = x :: children
                      vars = x :: vars
                      steps = (al <=> ar, have(proveExpr(al, ar, base))) :: steps
                      zip = (al, ar) :: zip
                    }
                  }
                  have(base.left |- (base.right + (l <=> l))) by Restate
                  val eqs = zip.map((l, r) => l <=> r)
                  val goal = have((base.left ++ eqs) |- (base.right + (l <=> r))).by.bot
                  have((base.left ++ eqs) |- (base.right + (l <=> r))) by RightSubstEq.withParameters(zip, lambda(vars, l <=> labelr.applyUnsafe(children)))(lastStep)
                  steps.foreach { s =>
                    have(
                      if s._2.bot.left.contains(s._1) then lastStep.bot else lastStep.bot -<< s._1
                    ) by Cut(s._2, lastStep)
                  }

                case (AppliedPredicate(labell, argsl), AppliedPredicate(labelr, argsr)) if labell == labelr && argsl.size == argsr.size =>
                  var freshn = freshId((l.freeVariableFormulas ++ r.freeVariableFormulas).map(_.id), "n").no
                  val ziped = (argsl zip argsr)
                  var zip = List[(Ind, Ind)]()
                  var children = List[Ind]()
                  var vars = List[Variable]()
                  var steps = List[(Prop, sp.ProofStep)]()
                  ziped.reverse.foreach { (al, ar) =>
                    if al == ar then children = al :: children
                    else {
                      val x = Variable(Identifier("n", freshn))
                      freshn = freshn + 1
                      children = x :: children
                      vars = x :: vars
                      steps = (al === ar, have(proveTerm(al, ar, base))) :: steps
                      zip = (al, ar) :: zip
                    }
                  }
                  have(base.left |- (base.right + (l <=> l))) by Restate
                  val eqs = zip.map((l, r) => l === r)
                  val goal = have((base.left ++ eqs) |- (base.right + (l <=> r))).by.bot
                  have((base.left ++ eqs) |- (base.right + (l <=> r))) by RightSubstEq.withParameters(zip, lambda(vars, l <=> labelr.applyUnsafe(children)))(lastStep)
                  steps.foreach { s =>
                    have(
                      if s._2.bot.left.contains(s._1) then lastStep.bot else lastStep.bot -<< s._1
                    ) by Cut(s._2, lastStep)
                  }
                case _ =>
                  println(s"l: $l")
                  println(s"r: $r")
                  throw UnreachableException

            }
            if id1 != l then
              val goalSequent = base.left |- (base.right + (id1 <=> r))
              val x = freshVariableFormula(id1)
              have(goalSequent +<< (l <=> r)) by RightSubstEq.withParameters(List((l, r)), lambda(x, id1 <=> x))(prev)
              have(goalSequent) by Cut(leqr, lastStep)

        }
    }
  }
   */

}
