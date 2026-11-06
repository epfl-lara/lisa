package lisa.benchmark

import org.openjdk.jmh.annotations.{Benchmark, BenchmarkMode, Fork, Measurement, Mode, Warmup}
import org.openjdk.jmh.infra.Blackhole
import lisa.kernel.proof.SCProofCheckerJudgement
import lisa.kernel.proof.SCProofChecker.checkSCProof
import org.openjdk.jmh.annotations.{State, Scope}

@State(Scope.Thread)
class SCProofBench:

  private val lib = lisa.SetTheoryLibrary

  import lisa.maths.SetTheory.*

  // theorems to use as targets for the benchmark ---
  // it should be noted that the sum of the chosen kernel proofs
  // should be reasonably large but shouldn't overwhelm the heap
  private val benchmarkBase: Seq[lib.THM] = Seq(
    // ... import chosen theorems to use as targets
    // Ordinals.TransfiniteRecursion.transfiniteRecursion,
    // Ordinals.TransfiniteInduction.transfiniteInduction,
    // Ordinals.Ordinal.hereditarilyTransitive,
    // Ordinals.Ordinal.hereditarilyWellOrdered,
    // Types.TypingTheorems.universeFamilyUnionClosure,
    // Types.TypingTheorems.universePiClosure,
    Order.WellOrders.WellOrderedRecursion.uniqueness,
    // Order.WellOrders.WellOrderedRecursion.coherence,
    // Order.WellOrders.WellOrderedRecursion.existence,
  )

  // precompute kernel proofs ---
  // this generally requires re-elaboration of the proofs,
  // so we have to do it before the benchmark
  private val scProofs = benchmarkBase.flatMap(_.kernelProof)

  @Benchmark
  @BenchmarkMode(Array(Mode.AverageTime))
  @Fork(value = 2)
  @Warmup(iterations = 5)
  @Measurement(iterations = 20)
  def scBench(blackHole: Blackhole): Seq[SCProofCheckerJudgement] = {
    val judgement = scProofs.map(checkSCProof)
    blackHole.consume(judgement)
    judgement
  }

end SCProofBench