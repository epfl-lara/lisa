package lisa.automation
import lisa.fol.FOL.{*, given}
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.prooflib.*

object Congruence {
  
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

class EGraphTerms() {

  type ENode = Term | Formula



  val termMap = mutable.Map[Term, Set[Term]]()
  val termParents = mutable.Map[Term, mutable.Set[AppliedFunction | AppliedPredicate]]()
  var termWorklist = List[Term]()
  val termUF = new UnionFind[Term]()




  val formulaMap = mutable.Map[Formula, Set[Formula]]()
  val formulaParents = mutable.Map[Formula, mutable.Set[AppliedConnector]]()
  var formulaWorklist = List[Formula]()
  val formulaUF = new UnionFind[Formula]()




  trait TermStep
  case class TermExternal(between: (Term, Term)) extends TermStep
  case class TermCongruence(between: (Term, Term)) extends TermStep

  trait FormulaStep
  case class FormulaExternal(between: (Formula, Formula)) extends FormulaStep
  case class FormulaCongruence(between: (Formula, Formula)) extends FormulaStep

  val termProofMap = mutable.Map[(Term, Term), TermStep]()
  val formulaProofMap = mutable.Map[(Formula, Formula), FormulaStep]()

  def explain(id1: Term, id2: Term): Option[List[TermStep]] = {
    val steps = termUF.explain(id1, id2)
    steps.map(_.foldLeft((id1, List[TermStep]())) {
      case ((prev, acc), step) =>
      termProofMap(step) match
        case s @ TermExternal((l, r)) => 
          if l == prev then
            (r, s :: acc)
          else if r == prev then
            (l, TermExternal(r, l) :: acc)
          else throw new Exception("Invalid proof recovered: It is not a chain")
        case s @ TermCongruence((l, r)) => 
          if l == prev then
            (r, s :: acc)
          else if r == prev then
            (l, TermCongruence(r, l) :: acc)
          else throw new Exception("Invalid proof recovered: It is not a chain")

    }._2.reverse)
  }

  def explain(id1: Formula, id2: Formula): Option[List[FormulaStep]] = {
    val steps = formulaUF.explain(id1, id2)
    steps.map(_.foldLeft((id1, List[FormulaStep]())) {
      case ((prev, acc), step) =>
      formulaProofMap(step) match
        case s @ FormulaExternal((l, r)) => 
          if l == prev then
            (r, s :: acc)
          else if r == prev then
            (l, FormulaExternal(r, l) :: acc)
          else throw new Exception("Invalid proof recovered: It is not a chain")
        case s @ FormulaCongruence((l, r)) => 
          if l == prev then
            (r, s :: acc)
          else if r == prev then
            (l, FormulaCongruence(r, l) :: acc)
          else throw new Exception("Invalid proof recovered: It is not a chain")

    }._2.reverse)
  }


  def makeSingletonEClass(node:Term): Term = {
    termUF.add(node)
    termMap(node) = Set(node)
    termParents(node) = mutable.Set()
    node
  }
  def makeSingletonEClass(node:Formula): Formula = {
    formulaUF.add(node)
    formulaMap(node) = Set(node)
    formulaParents(node) = mutable.Set()
    node
  }

  def classOf(id: Term): Set[Term] = termMap(id)
  def classOf(id: Formula): Set[Formula] = formulaMap(id)

  def idEq(id1: Term, id2: Term): Boolean = termUF.find(id1) == termUF.find(id2)
  def idEq(id1: Formula, id2: Formula): Boolean = formulaUF.find(id1) == formulaUF.find(id2)

  def canonicalize(node: Term): Term = node match
    case AppliedFunction(label, args) => 
      AppliedFunction(label, args.map(termUF.find.asInstanceOf))
    case _ => node
  
    
  def canonicalize(node: Formula): Formula = {
    node match
      case AppliedPredicate(label, args) => AppliedPredicate(label, args.map(termUF.find))
      case AppliedConnector(label, args) => AppliedConnector(label, args.map(formulaUF.find))
      case node => node
  }

  def add(node: Term): Term =
    if termMap.contains(node) then return node
    makeSingletonEClass(node)
    node match
      case node @ AppliedFunction(_, args) => 
        args.foreach(child => 
          add(child)
          termParents(child).add(node)
        )
        node
      case _ => node
  
  def add(node: Formula): Formula =
    if formulaMap.contains(node) then return node
    makeSingletonEClass(node)
    node match
      case node @ AppliedPredicate(_, args) => 
        args.foreach(child => 
          add(child)
          termParents(child).add(node)
        )
        node
      case node @ AppliedConnector(_, args) =>
        args.foreach(child => 
          add(child)
          formulaParents(child).add(node)
        )
        node
      case _ => node
    


  def merge(id1: Term, id2: Term): Unit = {
    mergeWithStep(id1, id2, TermExternal((id1, id2)))
  }
  def merge(id1: Formula, id2: Formula): Unit = {
    mergeWithStep(id1, id2, FormulaExternal((id1, id2)))
  }

  protected def mergeWithStep(id1: Term, id2: Term, step: TermStep): Unit = {
    if termUF.find(id1) == termUF.find(id2) then ()
    else
      termProofMap((id1, id2)) = step
      val newSet = termMap(termUF.find(id1)) ++ termMap(termUF.find(id2))
      val newparents = termParents(termUF.find(id1)) ++ termParents(termUF.find(id2))
      termUF.union(id1, id2)
      val newId1 = termUF.find(id1)
      val newId2 = termUF.find(id2)
      termMap(newId1) = newSet
      termMap(newId2) = newSet
      termParents(newId1) = newparents
      termParents(newId2) = newparents
      val id = termUF.find(id2)
      termWorklist = id :: termWorklist
      val cause = (id1, id2)
      val termSeen = mutable.Map[Term, AppliedFunction]()
      val formulaSeen = mutable.Map[Formula, Formula]()
      newparents.foreach { 
        case pTerm: AppliedFunction =>
          val canonicalPTerm = canonicalize(pTerm) 
          if termSeen.contains(canonicalPTerm) then 
            val qTerm = termSeen(canonicalPTerm)
            Some((pTerm, qTerm, cause))
            mergeWithStep(pTerm, qTerm, TermCongruence((pTerm, qTerm)))
          else
            termSeen(canonicalPTerm) = pTerm
        case pFormula: AppliedPredicate =>
          val canonicalPFormula = canonicalize(pFormula) 
          if formulaSeen.contains(canonicalPFormula) then 
            val qFormula = formulaSeen(canonicalPFormula)

            Some((pFormula, qFormula, cause))
            mergeWithStep(pFormula, qFormula, FormulaCongruence((pFormula, qFormula)))
          else
            formulaSeen(canonicalPFormula) = pFormula
      }
      termParents(id) = termSeen.values.to(mutable.Set)
  }

  protected def mergeWithStep(id1: Formula, id2: Formula, step: FormulaStep): Unit = 
    if formulaUF.find(id1) == formulaUF.find(id2) then ()
    else
      formulaProofMap((id1, id2)) = step
      val newSet = formulaMap(formulaUF.find(id1)) ++ formulaMap(formulaUF.find(id2))
      val newparents = formulaParents(formulaUF.find(id1)) ++ formulaParents(formulaUF.find(id2))
      formulaUF.union(id1, id2)
      val newId1 = formulaUF.find(id1)
      val newId2 = formulaUF.find(id2)
      formulaMap(newId1) = newSet
      formulaMap(newId2) = newSet
      formulaParents(newId1) = newparents
      formulaParents(newId2) = newparents
      val id = formulaUF.find(id2)
      formulaWorklist = id :: formulaWorklist
      val cause = (id1, id2)
      val formulaSeen = mutable.Map[Formula, AppliedConnector]()
      newparents.foreach { 
        case pFormula: AppliedConnector =>
          val canonicalPFormula = canonicalize(pFormula) 
          if formulaSeen.contains(canonicalPFormula) then 
            val qFormula = formulaSeen(canonicalPFormula)
            Some((pFormula, qFormula, cause))
            mergeWithStep(pFormula, qFormula, FormulaCongruence((pFormula, qFormula)))
          else
            formulaSeen(canonicalPFormula) = pFormula
      }
      formulaParents(id) = formulaSeen.values.to(mutable.Set)


  def prove(using lib: Library, proof: lib.Proof)(id1: Term, id2:Term, base: Sequent): proof.ProofTacticJudgement = 
    TacticSubproof { proveInner(id1, id2, base) }

  def proveInner(using lib: Library, proof: lib.Proof)(id1: Term, id2:Term, base: Sequent): Unit = {
    import lib.*
    val steps = explain(id1, id2)
    steps match {
      case None => throw new Exception("No proof found in the egraph")
      case Some(steps) => 
        if steps.isEmpty then have(base.left |- (base.right + (id1 === id2))) by Restate

        steps.foreach {
          case TermExternal((l, r)) => 
            val goalSequent = base.left |- (base.right + (id1 === r))
            if l == id1 then 
              have(goalSequent) by Restate
            else
              val x = freshVariable(id1)
              have(goalSequent) by RightSubstEq.withParametersSimple(List((l, r)), lambda(x, id1 === x))(lastStep)
          case TermCongruence((l, r)) => 
            ???
            /*
            val proof = prove(lib, proof)(l, r, base)
            proof match
              case Proof.ProofTacticJudgement(_, _, _, _, _) => ()
              case _ => throw new Exception("Invalid proof")
            */
        }
    }




  }


}