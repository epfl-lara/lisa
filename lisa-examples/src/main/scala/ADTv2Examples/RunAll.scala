package ADTv2Examples

import ADTv2Examples.builder.{DebugADTs, MonomorphicADTs, PolymorphicADTs, Specialization}
import ADTv2Examples.functions.{HigherOrderRecursion, RecursiveFunctions, SimpleFunctions}
import ADTv2Examples.proofs.{InductionOnBool, InductionOnNat, TypecheckIntegration}
import ADTv2Examples.endtoend.NatAndListLibrary
import lisa.maths.SetTheory.Types.ADTv2.support.Time

object RunAll {


  private val entries: Seq[(String, (Array[String] => Unit) | String)] = Seq(
    "ADTv2Examples.builder.MonomorphicADTs" -> MonomorphicADTs.main,
    "ADTv2Examples.builder.PolymorphicADTs" -> PolymorphicADTs.main,
    "ADTv2Examples.builder.Specialization" -> Specialization.main,
    "ADTv2Examples.builder.DebugADTs" -> DebugADTs.main,
    "ADTv2Examples.functions.SimpleFunctions" -> SimpleFunctions.main,
    "ADTv2Examples.functions.RecursiveFunctions" -> RecursiveFunctions.main,
    "ADTv2Examples.functions.HigherOrderRecursion" -> HigherOrderRecursion.main,
    "ADTv2Examples.proofs.InductionOnBool" -> InductionOnBool.main,
    "ADTv2Examples.proofs.InductionOnNat" -> InductionOnNat.main,
    "ADTv2Examples.proofs.TypecheckIntegration" -> TypecheckIntegration.main,
    "ADTv2Examples.endtoend.NatAndListLibrary" -> NatAndListLibrary.main
  )

  def main(args: Array[String]): Unit = {

    Time.reset()
    
    entries.foreach { (name, action) =>
      println(s"===== $name =====")
      action match
        case run: (Array[String] => Unit) =>
          val startedAt = Time.get()
          run(Array.empty)
          val finishedAt = Time.get()
          println(s"Execution of $name: ${finishedAt - startedAt}")
          Time.register(s"Execution of $name", finishedAt - startedAt)
        case reason: String =>
          println("Skipped: " + reason)
      println()
    }
    
    Time.printSummary()

  }
}
