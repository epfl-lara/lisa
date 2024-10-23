package lisa.automation
import lisa.fol.FOL.{*, given}
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.prooflib.*




///////////////////////////////
///////// E-graph /////////////
///////////////////////////////

import scala.collection.mutable





class EGraphExprSimp() {
  /*

  val termParents = mutable.Map[Term, mutable.Set[AppliedFunctional]]()
  val termUF = new UnionFind[Term]()
  val termProofMap = mutable.Map[(Term, Term), Boolean]()



  def find(id: Term): Term = termUF.find(id)
    
  def add(node: Term): Term =
    termUF.add(node)
    termParents(node) = mutable.Set()
    node match
      case node @ AppliedFunctional(_, args) => 
        
        args.foreach(child => 
          add(child)
          termParents(child).add(node)
        )
        node
      case _ => node


  def merge(id1: Term, id2: Term): Unit = {
    mergeWithStep(id1, id2, true)
  }

  type Sig = (TermLabel[?]|Term, List[Int])
  val termSigs = mutable.Map[Sig, Term]()
  val codes = mutable.Map[Term, Int]()

  protected def mergeWithStep(id1: Term, id2: Term, isExternal: Boolean): Unit = {
    if find(id1) == find(id2) then return ()
    termProofMap((id1, id2)) = isExternal
    val (small, big ) = if termParents(find(id1)).size < termParents(find(id2)).size then
      (id1, id2) else (id2, id1)
    codes(find(small)) = codes(find(big))
    termUF.union(id1, id2)
    val newId = find(id1)
    var worklist = List[(Term, Term, Boolean)]()

    termParents(small).foreach { pTerm =>
      val canonicalPTerm = canonicalize(pTerm) 
      if termSigs.contains(canonicalPTerm) then 
        val qTerm = termSigs(canonicalPTerm)
        mergeWithStep(pTerm, qTerm, false)
      else
        termSigs(canonicalPTerm) = pTerm
    }
    termParents(newId) = termParents(big)
    termParents(newId).addAll(termParents(small))
  }

  def canonicalize(node: Term): Sig = node match
    case AppliedFunctional(label, args) => 
      (label, args.map(a => codes(find(a))).toList)
    case _ => (node, List())




  // Explain




  def explain(id1: Term, id2: Term): Option[List[(Term, Term, Boolean)]] = {
    val steps = termUF.explain(id1, id2)
    steps.map(_.map { a => (a._1, a._2, termProofMap(a))

    })
  }











  // Proofs Lisa

  def proveTerm(using lib: Library, proof: lib.Proof)(id1: Term, id2:Term, base: Sequent): proof.ProofTacticJudgement = 
    TacticSubproof { proveInnerTerm(id1, id2, base) }

  def proveInnerTerm(using lib: Library, proof: lib.Proof)(id1: Term, id2:Term, base: Sequent): Unit = {
    import lib.*
    val steps = explain(id1, id2)
    steps match {
      case None => throw new Exception("No proof found in the egraph")
      case Some(steps) => // External
        have(base.left |- (base.right + (id1 === id2))) by Restate
        var current = id1
        steps.foreach {
          case (l, r, true) => 
            current = if current == l then r else l 
            val goalSequent = base.left |- (base.right + (id1 === r))
            val x = freshVariable(id1)
            //thenHave(id1 === current) by Transitivity(l === r)
            have(goalSequent) by RightSubstEq.withParametersSimple(List((l, r)), lambda(x, id1 === x))(lastStep)
          case (l, r, false) => // Congruence
            val prev = lastStep
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
            val goalSequent = base.left |- (base.right + (id1 === r))
            val x = freshVariable(id1)
            have(goalSequent +<< (l === r)) by RightSubstEq.withParametersSimple(List((l, r)), lambda(x, id1 === x))(prev)
            have(goalSequent) by Cut(leqr, lastStep)
        }
    }
  }
*/

}