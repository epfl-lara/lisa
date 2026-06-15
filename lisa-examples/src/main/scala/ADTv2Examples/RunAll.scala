package ADTv2Examples

import ADTv2Examples.builder.{DebugADTs, MonomorphicADTs, PolymorphicADTs, Specialization}
import ADTv2Examples.functions.{HigherOrderRecursion, RecursiveFunctions, SimpleFunctions, NestedPatterns}
import ADTv2Examples.proofs.{SimpleInduction, NestedPatternInduction, TypecheckIntegration, Injectivity, Computation}
import ADTv2Examples.endtoend.{NatAndListLibrary, LibraryFeatures}
import ADTv2Examples.overview.FeatureTour
import lisa.maths.SetTheory.Types.ADTv2.support.Time

object RunAll {

  sealed trait Entry
  object Entry {
    final case class Init(run: () => Unit) extends Entry
    final case class Main(run: Array[String] => Unit) extends Entry
    final case class Skip(reason: String) extends Entry
  }

  private val entries: Seq[(String, Entry)] = Seq(
    "ADTv2.height.proofs.ProofsInitialization" ->
      Entry.Init(lisa.maths.SetTheory.Types.ADTv2.height.proofs.ProofsInitialization.initialize),
    "ADTv2.recursion.proofs.ProofsInitialization" ->
      Entry.Init(lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ProofsInitialization.initialize),
    "ADTv2Examples.builder.MonomorphicADTs" -> Entry.Main(MonomorphicADTs.main),
    "ADTv2Examples.builder.PolymorphicADTs" -> Entry.Main(PolymorphicADTs.main),
    "ADTv2Examples.builder.Specialization" -> Entry.Main(Specialization.main),
    "ADTv2Examples.builder.DebugADTs" -> Entry.Skip("Debugs ADTs are only used for performance testing"),
    "ADTv2Examples.functions.SimpleFunctions" -> Entry.Main(SimpleFunctions.main),
    "ADTv2Examples.functions.RecursiveFunctions" -> Entry.Main(RecursiveFunctions.main),
    "ADTv2Examples.functions.HigherOrderRecursion" -> Entry.Main(HigherOrderRecursion.main),
    "ADTv2Examples.functions.NestedPatterns" -> Entry.Main(NestedPatterns.main),
    "ADTv2Examples.proofs.TypecheckIntegration" -> Entry.Main(TypecheckIntegration.main),
    "ADTv2Examples.proofs.SimpleInduction" -> Entry.Main(SimpleInduction.main),
    "ADTv2Examples.proofs.NestedPatternInduction" -> Entry.Main(NestedPatternInduction.main),
    "ADTv2Examples.proofs.Injectivity" -> Entry.Main(Injectivity.main),
    "ADTv2Examples.proofs.Computation" -> Entry.Main(Computation.main),
    "ADTv2Examples.endtoend.NatAndListLibrary" -> Entry.Main(NatAndListLibrary.main),
    "ADTv2Examples.endtoend.LibraryFeatures" -> Entry.Main(LibraryFeatures.main),
    "ADTv2Examples.overview.FeatureTour" -> Entry.Main(FeatureTour.main)
  )

  def main(args: Array[String]): Unit = {

    Time.reset()

    entries.foreach { (name, action) =>
      println(s"===== $name =====")
      action match
        case Entry.Init(run) =>
          Time.measure("Initialization", true)(run())
        case Entry.Main(run) =>
          val startedAt = Time.get()
          run(Array.empty)
          val finishedAt = Time.get()
          println(s"Execution of $name: ${finishedAt - startedAt}")
          // Time.register(s"Execution of $name", finishedAt - startedAt)
        case Entry.Skip(reason) =>
          println("Skipped: " + reason)
      println()
    }

    // Time.printSummary()
    Time.printTree(selfAsChild = true)

  }
}
