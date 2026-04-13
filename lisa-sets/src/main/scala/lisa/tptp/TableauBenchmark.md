# TableauBenchmark

Benchmarks `Tableau.solve` on TPTP problems with timing, proof verification, and multiple output formats.

## Prerequisites

Set the `TPTP` environment variable to the full TPTP distribution root (needed for problems with `include` directives):

```bash
export TPTP=/path/to/TPTP-v9.2.1
```

## Command line (via sbt)

```bash
# Default text output
sbt "lisa-sets/runMain lisa.tptp.TableauBenchmark --input tptp-pure-fol/SYN/SYN048+1.p"

# Verbose output
sbt "lisa-sets/runMain lisa.tptp.TableauBenchmark --input tptp-pure-fol/SYN/SYN048+1.p --format verbose"

# CSV output
sbt "lisa-sets/runMain lisa.tptp.TableauBenchmark --input tptp-pure-fol/SYN/SYN048+1.p --format csv"

# Custom timeout (ms, default 60000, 0 = no timeout)
sbt "lisa-sets/runMain lisa.tptp.TableauBenchmark --input tptp-pure-fol/SYN/SYN048+1.p --timeout 30000"

# Skip proof verification
sbt "lisa-sets/runMain lisa.tptp.TableauBenchmark --input tptp-pure-fol/SYN/SYN048+1.p --verify false"
```

## From Scala

```scala
import lisa.tptp.TableauBenchmark
import java.io.File

val result = TableauBenchmark.runBenchmark(
  problemFile = File("tptp-pure-fol/SYN/SYN048+1.p"),
  timeoutMs = 60000,  // 0 = no timeout
  verify = true        // check proof with kernel
)

println(result.solved)      // Boolean
println(result.solveTimeMs) // Long
println(result.proofSteps)  // Option[Int]
println(result.proofValid)  // Option[Boolean]
println(result.error)       // Option[String]
```

`BenchmarkResult` also has `.toCSV` and `.toCSVHeader` for batch processing.
