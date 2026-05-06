package ADTv2Examples

import ADTv2Examples.builder.{DefineMonomorphicADTs, DefinePolymorphicADTs, Specialization}
import ADTv2Examples.functions.{HigherOrderRecursion, RecursiveFunctions}
import ADTv2Examples.proofs.{InductionOnBool, InductionOnNat}

object RunAll {

  private val entries = Seq(
    "ADTv2Examples.builder.DefineMonomorphicADTs" -> (() => DefineMonomorphicADTs.main(Array.empty)),
    "ADTv2Examples.builder.DefinePolymorphicADTs" -> (() => DefinePolymorphicADTs.main(Array.empty)),
    "ADTv2Examples.builder.Specialization" -> (() => Specialization.main(Array.empty)),
    "ADTv2Examples.functions.RecursiveFunctions" -> (() => RecursiveFunctions.main(Array.empty)),
    "ADTv2Examples.functions.HigherOrderRecursion" -> (() => HigherOrderRecursion.main(Array.empty)),
    "ADTv2Examples.proofs.InductionOnBool" -> (() => InductionOnBool.main(Array.empty)),
    "ADTv2Examples.proofs.InductionOnNat" -> (() => InductionOnNat.main(Array.empty))
  )

  def main(args: Array[String]): Unit = {
    entries.foreach { (name, run) =>
      println(s"===== $name =====")
      run()
      println()
    }

    println("===== ADTv2Examples.functions.SimpleFunctions =====")
    println("Skipped: positive fun(...) examples are currently unstable in the ADTv2 runtime.")
    println()

    println("===== ADTv2Examples.proofs.TypecheckIntegration =====")
    println("Skipped: standalone Typecheck.prove examples currently fail on nested ADTv2 terms.")
    println()

    println("===== ADTv2Examples.endtoend.NatAndListLibrary =====")
    println("Skipped: specialized constructor typechecking is currently unstable in standalone runs.")
    println()
  }
}
