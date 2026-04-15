package lisa.automation.TableauBench

import lisa.automation.Tableau
import lisa.tptp.KernelParser._
import lisa.utils.K
import lisa.utils.K.{_, given}
import lisa.utils.KernelHelpers._

import java.io.File

object DiagnosticRun {
  def main(args: Array[String]): Unit = {
    Tableau.debug = false
    
    val problemPath = if args.nonEmpty then args(0) else "tptp-pure-fol/SYN/SYN326+1.p"
    val file = new File(problemPath)
    val resolvedFile = if (file.isAbsolute || file.exists()) file
      else new File(sys.props.getOrElse("user.dir", ".")).getParentFile match
        case null => file
        case parent => val candidate = new File(parent, problemPath); if candidate.exists() then candidate else file
    
    System.err.println(s"File: ${resolvedFile.getAbsolutePath}, exists: ${resolvedFile.exists()}")
    
    val prob = problemToKernel(resolvedFile)(using strictMapAtom, strictMapTerm, strictMapVariable)
    val sequent = problemToSequent(prob)
    System.err.println(s"Sequent left: ${sequent.left.size}, right: ${sequent.right.size}")
    
    // Replicate solve's preprocessing 
    val f = K.multiand(sequent.left.toSeq ++ sequent.right.map(f => K.neg(f)))
    val taken = f.allVariables
    val nextIdNow = if taken.isEmpty then 0 else taken.maxBy(_.id.no).id.no + 1
    val (fnamed, nextId) = Tableau.makeVariableNamesUnique(f, nextIdNow, f.freeVariables)
    val nf = K.reducedNNFForm(fnamed)
    System.err.println(s"NNF formula (first 300 chars): ${K.repr(nf).take(300)}")
    
    // Count formula structure
    def countStructure(e: K.Expression): (Int, Int, Int, Int, Int) = e match
      case K.And(l, r) => val (a1,b1,d1,g1,at1) = countStructure(l); val (a2,b2,d2,g2,at2) = countStructure(r); (a1+a2+1, b1+b2, d1+d2, g1+g2, at1+at2)
      case K.Or(l, r) => val (a1,b1,d1,g1,at1) = countStructure(l); val (a2,b2,d2,g2,at2) = countStructure(r); (a1+a2, b1+b2+1, d1+d2, g1+g2, at1+at2)
      case K.Exists(_, inner) => val (a,b,d,g,at) = countStructure(inner); (a, b, d+1, g, at)
      case K.Forall(_, inner) => val (a,b,d,g,at) = countStructure(inner); (a, b, d, g+1, at)
      case _ => (0, 0, 0, 0, 1)
    
    val (alphas, betas, deltas, gammas, atoms) = countStructure(nf)
    System.err.println(s"NNF structure: alphas=$alphas, betas=$betas, deltas=$deltas, gammas=$gammas, atoms=$atoms")
    
    val uv = K.Variable(K.Identifier("§", nextId), K.Ind)
    
    // Test with various budgets - run in thread with large stack
    val tests = Seq((1, 100), (1, 1000), (1, 5000), (1, 20000), (2, 1000), (2, 5000), (2, 20000), (2, 100000), (3, 20000), (3, 100000), (5, 500000))
    val thread = new Thread(null, () => {
      for ((instLimit, budget) <- tests) {
        Tableau.decideBudget.set(budget)
        val t0 = System.currentTimeMillis()
        val result = Tableau.decide(Tableau.Branch.empty(nextId + 1, uv, instLimit).prepended(nf))
        val t1 = System.currentTimeMillis()
        val used = budget - Tableau.decideBudget.get()
        System.err.println(s"  instLimit=$instLimit, budget=$budget, used=$used, found=${result.isDefined}, time=${t1-t0}ms")
        if (result.isDefined) {
          System.err.println(s"  >>> PROOF FOUND at instLimit=$instLimit with $used decide calls!")
          return
        }
      }
    }, "diagnostic-thread", 64 * 1024 * 1024)
    thread.start()
    thread.join(120000) // 2 minute timeout
    if (thread.isAlive) {
      thread.interrupt()
      System.err.println("  >>> Timed out after 120 seconds")
    }
    
    System.err.println("=== Done ===")
  }
}
