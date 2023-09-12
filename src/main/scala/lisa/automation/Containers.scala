package lisa.automation

import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.kernel.proof.SequentCalculus as SC
import lisa.mathematics.settheory.SetTheory
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.{_, given}
import lisa.prooflib.*
import lisa.settheory.SetTheoryLibrary
import lisa.utils.KernelHelpers.*
import lisa.utils.Printer

object Containers {
  /*
  import lisa.settheory.SetTheoryLibrary.{_, given}

  case class Value(name:String, property:LambdaTermFormula){
    require(property.vars.sie == 1)
  }

  def defineContainer(using om: OutputManager)(name:String, values:Seq[Value]): ConstantFunctionLabel = {
    val funl = ConstantFunctionLabel(name, values.length)

    //THM(using om: OutputManager)(statement: Sequent | String, val fullName: String, line: Int, file: String, val kind: TheoremKind)(computeProof: Proof ?=> Unit)

    val variables = values.map(_.property.vars.head)
    val statement = existsOne(z)
    val funlExistsThm = Theorem.apply()

  }
   */
}
