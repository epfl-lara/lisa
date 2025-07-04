package lisa.automation
import lisa.fol.FOL.{*, given}
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.prooflib.*
import leo.datastructures.TPTP.CNF.AtomicFormula
import scala.annotation.targetName

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
  * 
  */
object Congruence  extends ProofTactic with ProofSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(bot: Sequent): proof.ProofTacticJudgement = TacticSubproof {
      import lib.*

      val egraph = new EGraphExpr()
      egraph.addAll(bot.left)
      egraph.addAll(bot.right)

      bot.left.foreach{
        case (left === right) => egraph.merge(left, right)
        case (left <=> right) => egraph.merge(left, right)
        case _ => ()
      }

      if isSameSequent(bot, ⊤) then
        have(bot) by Restate
      else if bot.left.exists { lf =>
        bot.right.exists { rf =>
          if egraph.idEq(lf, rf) then
            val base = have(bot.left |- (bot.right + lf) ) by Restate
            val eq = have(egraph.proveFormula(lf, rf, bot))
            val a = variable[Formula]
            val eqstep = have((lf <=> rf) |- (lf <=> rf)) by Restate
            have((bot.left + (lf <=> rf)) |- (bot.right) ) by RightSubstIff.withParametersSimple(lf, rf, Seq(), (a, a))(base, eqstep)
            have(bot) by Cut(eq, lastStep)
            true
          else false
        } ||
        bot.left.exists{ 
          case rf2 @ neg(rf) if egraph.idEq(lf, rf)=>
            val base = have((bot.left + !lf) |- bot.right ) by Restate
            val eq = have(egraph.proveFormula(lf, rf, bot))
            val a = variable[Formula]
            val eqstep = have((lf <=> rf) |- (lf <=> rf)) by Restate
            have((bot.left + (lf <=> rf)) |- (bot.right) ) by LeftSubstIff.withParametersSimple(lf, rf, Seq(), (a, !a))(base, eqstep)
            have(bot) by Cut(eq, lastStep)
            true
          case _  => false
        } || {
        lf match
          case !(a === b) if egraph.idEq(a, b) => 
            have(egraph.proveTerm(a, b, bot))
            true
          case !(a <=> b) if egraph.idEq(a, b) => 
            have(egraph.proveFormula(a, b, bot))
            true
          case _ => false
        }

      } then ()
      else if bot.right.exists { rf =>
        bot.right.exists{ 
          case lf2 @ neg(lf) if egraph.idEq(lf, rf)=>
            val base = have((bot.left) |- (bot.right + !rf) ) by Restate
            val eq = have(egraph.proveFormula(lf, rf, bot))
            val a = variable[Formula]
            val eqstep = have((lf <=> rf) |- (lf <=> rf)) by Restate
            have((bot.left + (lf <=> rf)) |- (bot.right) ) by RightSubstIff.withParametersSimple(lf, rf, Seq(), (a, !a))(base, eqstep)
            have(bot) by Cut(eq, lastStep)
            true
          case _  => false
        } || {
        rf match
          case (a === b) if egraph.idEq(a, b) => 
            have(egraph.proveTerm(a, b, bot))
            true
          case (a <=> b) if egraph.idEq(a, b) =>
            have(egraph.proveFormula(a, b, bot))
            true
          case _ => false
        }
      } then ()
      else
        return proof.InvalidProofTactic(s"No congruence found to show sequent\n $bot")
    }

  
}


class UnionFind[T]  {
  // parent of each element, leading to its root. Uses path compression
  val parent = scala.collection.mutable.Map[T, T]()
  // original parent of each element, leading to its root. Does not use path compression. Used for explain.
  val realParent = scala.collection.mutable.Map[T, (T, ((T, T), Boolean, Int))]()
  //keep track of the rank (i.e. number of elements bellow it) of each element. Necessary to optimize union.
  val rank = scala.collection.mutable.Map[T, Int]()
  //tracks order of ancientness of unions.
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
    *
    * @param x the element whose parent we want to find
    * @return the root of x
    */
  def find(x: T): T = {
    if parent(x) == x then
      x
    else
      var root = x
      while parent(root) != root do
        root = parent(root)
      var y = x
      while parent(y) != root do
        parent(y) = root
        y = parent(y)
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
    if x == find(x) then
      List(x)
    else
      val next = realParent(x)
      x :: getPathToRoot(next._1)

  }

  private def getExplanationFromTo(x:T, c: T): List[(T, ((T, T), Boolean, Int))] = {
    if x == c then
      List()
    else
      val next = realParent(x)
      next :: getExplanationFromTo(next._1, c)}

  private def lowestCommonAncestor(x: T, y: T): Option[T] = {
    val pathX = getPathToRoot(x)
    val pathY = getPathToRoot(y)
    pathX.find(pathY.contains)
  }

  /**
    * Returns a path from x to y made of pairs of elements (u, v)
    * such that union(u, v) was called.
    */
  def explain(x:T, y:T): Option[List[(T, T)]]= {

    if (x == y) then return Some(List())
    val lca = lowestCommonAncestor(x, y)
    lca match
      case None => None
      case Some(lca) =>
        var max :((T, T), Boolean, Int) = ((x, x), true, 0)
        var itX = x
        while itX != lca do
          val (next, ((u1, u2), b, c)) = realParent(itX)
          if c > max._3 then
            max = ((u1, u2), b, c)
          itX = next

        var itY = y
        while itY != lca do
          val (next, ((u1, u2), b, c)) = realParent(itY)
          if c > max._3 then
            max = ((u1, u2), !b, c)
          itY = next

        val u1 = max._1._1
        val u2 = max._1._2
        if max._2 then
          Some(explain(x, u1).get ++ List((u1, u2)) ++ explain(u2, y).get)
        else
          Some(explain(x, u2).get ++ List((u1, u2)) ++ explain(u1, y).get)
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

  val parents = mutable.Map[Expr[?], mutable.Set[App[?, ?]]]()
  val UF = new UnionFind[Expr[?]]()




  def find[T](id: Expr[T]): Expr[T] = UF.find(id).asInstanceOf[Expr[T]]

  trait Step
  case class ExternalStep(between: (Expr[?], Expr[?])) extends Step
  case class CongruenceStep(between: (Expr[?], Expr[?])) extends Step


  val proofMap = mutable.Map[(Expr[?], Expr[?]), Step]()

  def explain(id1: Expr[?], id2: Expr[?]): Option[List[Step]] = {
    val steps = UF.explain(id1, id2)
    steps.map(_.foldLeft((id1, List[Step]())) {
      case ((prev, acc), step) =>
      proofMap(step) match
        case s @ ExternalStep((l, r)) => 
          if l == prev then
            (r, s :: acc)
          else if r == prev then
            (l, ExternalStep(r, l) :: acc)
          else throw new Exception("Invalid proof recovered: It is not a chain")
        case s @ CongruenceStep((l, r)) => 
          if l == prev then
            (r, s :: acc)
          else if r == prev then
            (l, CongruenceStep(r, l) :: acc)
          else throw new Exception("Invalid proof recovered: It is not a chain")

    }._2.reverse)
  }


  def makeSingletonEClass(node:Expr[?]): Expr[?] = {
    UF.add(node)
    parents(node) = mutable.Set()
    node
  }

  def idEqT(id1: Term, id2: Term): Boolean = find(id1) == find(id2)
  def idEqF(id1: Formula, id2: Formula): Boolean = find(id1) == find(id2)

  

  def canonicalize(node: Expr[?]): Expr[?] = node match
    case node @ App(f, a) => App.unsafe(find(f), find(a))
    case _ => node
  
    

  def add(node: Expr[?]): Expr[?] =
    if UF.parent.contains(node) then return node
    makeSingletonEClass(node)
    codes(node) = codes.size
    node match
      case node @ App(f, a) =>
        add(f)
        parents(find(f)).add(node)
        add(a)
        parents(find(a)).add(node)
      case _ => ()
    termSigs(canSig(node)) = node
    node


  def addAll(nodes: Iterable[Term|Formula]): Unit = 
    nodes.foreach{
      case node: Term => add(node)
      case node: Formula => add(node)
    }
    
    


  def merge(id1: Expr[?], id2: Expr[?]): Unit = {
    mergeWithStep(id1, id2, ExternalStep((id1, id2)))
  }

  type Sig = Expr[?] | (Int, Int)
  val termSigs = mutable.Map[Sig, Expr[?]]()
  val codes = mutable.Map[Expr[?], Int]()

  def canSig(node: Expr[?]): Sig = node match
    case App(f, g) => (codes(find(f)), codes(find(g)))
    case _ => node

  protected def mergeWithStep(id1: Expr[?], id2: Expr[?], step: Step): Unit = {
    if id1.sort != id2.sort then throw new IllegalArgumentException("Cannot merge nodes of different sorts")
    if find(id1) == find(id2) then ()
    else
      proofMap((id1, id2)) = step
      val parents1 = parents(find(id1))
      val parents2 = parents(find(id2))


    if find(id1) == find(id2) then return ()

    proofMap((id1, id2)) = step
    val (small, big ) = if parents(find(id1)).size < parents(find(id2)).size then
      (id1, id2) else (id2, id1)
    codes(find(small)) = codes(find(big))
    UF.union(id1, id2)
    val newId = find(id1)
    var worklist = List[(Expr[?], Expr[?], Step)]()

    parents(small).foreach { pExpr =>
      val canonicalPExpr = canSig(pExpr) 
      if termSigs.contains(canonicalPExpr) then 
        val qExpr = termSigs(canonicalPExpr)

        worklist = (pExpr, qExpr, CongruenceStep((pExpr, qExpr))) :: worklist
      else
        termSigs(canonicalPExpr) = pExpr
    }
    parents(newId) = parents(big)
    parents(newId).addAll(parents(small))
    worklist.foreach { case (l, r, step) => mergeWithStep(l, r, step) }
  }



  def proveTerm[S](using lib: Library, proof: lib.Proof)(id1: Expr[S], id2:Expr[S], base: Sequent): proof.ProofTacticJudgement = 
    TacticSubproof { proveInner(id1, id2, base) }

  def proveInner[S](using lib: Library, proof: lib.Proof)(id1: Expr[S], id2:Expr[S], base: Sequent): Unit = {
    import lib.*
    val steps = explain(id1, id2)
    val sort = id1.sort
    val (eqOp, vars) = sort match
      case Functional(argSorts) =>
        ???
      case Predicate(argSorts) =>
        ???
    
    steps match {
      case None => throw new Exception("No proof found in the egraph")

      case Some(steps) => 
        if steps.isEmpty then have(base.left |- (base.right + (id1 === id2))) by Restate
        steps.foreach {
          case ExternalStep((l, r)) => 
            val goalSequent = base.left |- (base.right + (id1 === r))
            if l == id1 then 
              have(goalSequent) by Restate
            else
              val x = freshVariable(id1)
              have(goalSequent) by RightSubstEq.withParametersSimple(List((l, r)), lambda(x, id1 === x))(lastStep)
          case CongruenceStep((l, r)) => 
            val prev = if id1 != l then lastStep else null
            val leqr = have(base.left |- (base.right + (l === r))) subproof { sp ?=>
              (l, r) match
                case (AppliedFunctional(labell, argsl), AppliedFunctional(labelr, argsr)) if labell == labelr && argsl.size == argsr.size => 
                  var freshn = freshId((l.freeVariables ++ r.freeVariables).map(_.id), "n").no
                  val ziped = (argsl zip argsr)
                  var zip = List[(Term, Term)]()
                  var children = List[Term]()
                  var vars = List[Variable]()
                  var steps = List[(Formula, sp.ProofStep)]()
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
                  have(base.left |- (base.right + (l === l))) by Restate
                  val eqs = zip.map((l, r) => l === r)
                  val goal = have((base.left ++ eqs) |- (base.right + (l === r))).by.bot
                  have((base.left ++ eqs) |- (base.right + (l === r))) by RightSubstEq.withParametersSimple(zip, lambda(vars, l === labelr.applyUnsafe(children)))(lastStep)
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
              val goalSequent = base.left |- (base.right + (id1 === r))
              val x = freshVariable(id1)
              have(goalSequent +<< (l === r)) by RightSubstEq.withParametersSimple(List((l, r)), lambda(x, id1 === x))(prev)
              have(goalSequent) by Cut(leqr, lastStep)
        }
    }
  }

  def proveFormula(using lib: Library, proof: lib.Proof)(id1: Formula, id2:Formula, base: Sequent): proof.ProofTacticJudgement = 
    TacticSubproof { proveInnerFormula(id1, id2, base) }

  def proveInnerFormula(using lib: Library, proof: lib.Proof)(id1: Formula, id2:Formula, base: Sequent): Unit = {
    import lib.*
    val steps = explain(id1, id2)
    steps match {
      case None => throw new Exception("No proof found in the egraph")
      case Some(steps) => 
        if steps.isEmpty then have(base.left |- (base.right + (id1 <=> id2))) by Restate
        steps.foreach {
          case FormulaExternal((l, r)) => 
            val goalSequent = base.left |- (base.right + (id1 <=> r))
            if l == id1 then 
              have(goalSequent) by Restate
            else
              val x = freshVariableFormula(id1)
              have(goalSequent) by RightSubstIff.withParametersSimple(List((l, r)), lambda(x, id1 <=> x))(lastStep)
          case FormulaCongruence((l, r)) => 
            val prev = if id1 != l then lastStep else null
            val leqr = have(base.left |- (base.right + (l <=> r))) subproof { sp ?=>
              (l, r) match
                case (AppliedConnector(labell, argsl), AppliedConnector(labelr, argsr)) if labell == labelr && argsl.size == argsr.size => 
                  var freshn = freshId((l.freeVariableFormulas ++ r.freeVariableFormulas).map(_.id), "n").no
                  val ziped = (argsl zip argsr)
                  var zip = List[(Formula, Formula)]()
                  var children = List[Formula]()
                  var vars = List[VariableFormula]()
                  var steps = List[(Formula, sp.ProofStep)]()
                  ziped.reverse.foreach { (al, ar) =>
                    if al == ar then children = al :: children
                    else {
                      val x = VariableFormula(Identifier("n", freshn))
                      freshn = freshn + 1
                      children = x :: children
                      vars = x :: vars
                      steps = (al <=> ar, have(proveFormula(al, ar, base))) :: steps
                      zip = (al, ar) :: zip
                    }
                  }
                  have(base.left |- (base.right + (l <=> l))) by Restate
                  val eqs = zip.map((l, r) => l <=> r)
                  val goal = have((base.left ++ eqs) |- (base.right + (l <=> r))).by.bot
                  have((base.left ++ eqs) |- (base.right + (l <=> r))) by RightSubstIff.withParametersSimple(zip, lambda(vars, l <=> labelr.applyUnsafe(children)))(lastStep)
                  steps.foreach { s =>
                    have(
                      if s._2.bot.left.contains(s._1) then lastStep.bot else lastStep.bot -<< s._1
                    ) by Cut(s._2, lastStep)
                  }

                case (AppliedPredicate(labell, argsl), AppliedPredicate(labelr, argsr)) if labell == labelr && argsl.size == argsr.size => 
                  var freshn = freshId((l.freeVariableFormulas ++ r.freeVariableFormulas).map(_.id), "n").no
                  val ziped = (argsl zip argsr)
                  var zip = List[(Term, Term)]()
                  var children = List[Term]()
                  var vars = List[Variable]()
                  var steps = List[(Formula, sp.ProofStep)]()
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
                  have((base.left ++ eqs) |- (base.right + (l <=> r))) by RightSubstEq.withParametersSimple(zip, lambda(vars, l <=> labelr.applyUnsafe(children)))(lastStep)
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
              have(goalSequent +<< (l <=> r)) by RightSubstIff.withParametersSimple(List((l, r)), lambda(x, id1 <=> x))(prev)
              have(goalSequent) by Cut(leqr, lastStep)
        
        }
    }
  }


}