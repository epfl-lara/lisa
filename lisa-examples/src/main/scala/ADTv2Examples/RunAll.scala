package ADTv2Examples

import ADTv2Examples.builder.{DefineMonomorphicADTs, DefinePolymorphicADTs, Specialization}
import ADTv2Examples.functions.{HigherOrderRecursion, RecursiveFunctions}
import ADTv2Examples.proofs.{InductionOnBool, InductionOnNat, TypecheckIntegration}
import lisa.maths.SetTheory.Types.ADTv2.support.Time

object RunAll {


  private val entries: Seq[(String, (Array[String] => Unit) | String)] = Seq(
    "ADTv2Examples.builder.DefineMonomorphicADTs" -> DefineMonomorphicADTs.main,
    "ADTv2Examples.builder.DefinePolymorphicADTs" -> "Crash for now", //DefinePolymorphicADTs.main,
    "ADTv2Examples.builder.Specialization" -> Specialization.main,
    "ADTv2Examples.functions.SimpleFunctions" -> "positive fun(...) examples are currently unstable in the ADTv2 runtime.",
    "ADTv2Examples.functions.RecursiveFunctions" -> RecursiveFunctions.main,
    "ADTv2Examples.functions.HigherOrderRecursion" -> HigherOrderRecursion.main,
    "ADTv2Examples.proofs.InductionOnBool" -> InductionOnBool.main,
    "ADTv2Examples.proofs.InductionOnNat" -> InductionOnNat.main,
    "ADTv2Examples.proofs.TypecheckIntegration" -> TypecheckIntegration.main,
    "ADTv2Examples.endtoend.NatAndListLibrary" -> "specialized constructor typechecking is currently unstable in standalone runs."
  )

  def main(args: Array[String]): Unit = {
    entries.foreach { (name, action) =>
      println(s"===== $name =====")
      action match
        case run: (Array[String] => Unit) =>
          val startedAt = Time.get()
          run(Array.empty)
          val finishedAt = Time.get()
          println(s"Execution time: ${finishedAt - startedAt}")
        case reason: String =>
          println("Skipped: " + reason)
      println()
    }
  }
}
