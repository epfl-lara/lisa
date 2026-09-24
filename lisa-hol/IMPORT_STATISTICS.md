# Measure HOL reconstruction

Read the progress line after each named theorem. `steps/s` counts newly
reconstructed HOL trace steps, not Lisa kernel steps or cache hits. An alias
can therefore report zero steps. The cumulative rate includes earlier reporting;
the last-theorem rate measures that theorem's reconstruction and registration.

Use the additional counters to distinguish expensive proofs from runtime stalls:

- **CPU:** importer-thread CPU time for the last theorem.
- **Allocated:** bytes allocated by that thread, including objects subsequently
  collected; this is not retained heap. KiB/step normalizes it by new HOL steps.
- **GC:** the increase in JVM-wide collection time reported by management beans.
  Use JVM GC logs for precise pause measurements.
- **Reused:** lookups satisfied by the shared reconstructed-step cache.
- **Heap used:** a snapshot, not a post-GC live-set measurement.

Collect detailed costs with a fresh CSV output path:

```sh
java -Xmx10G -Dlisa.hol.stats=/tmp/hol-rules.csv \
  -cp lisa-hol/target/scala-3.7.2/lisa-hol-assembly-0.9.3.jar \
  lisa.hol.ImportBenchmark /path/to/export-prefix 535
```

Alternatively, set `LISA_HOL_STATS` in the importing JVM's environment. An
already-running sbt server may not inherit a newly set shell variable. The Java
property takes precedence. Existing CSV files are never overwritten.

The CSV contains one row per theorem and rule/phase, flushed after each attempt:
count, thrown exceptions, exclusive wall time, exclusive thread CPU time,
exclusive allocated bytes, and the slowest exclusive operation's time/trace ID.
Times are nanoseconds. Unsupported CPU/allocation measurements use `-1`.
`read` covers extractor calls; `named` covers final theorem translation,
checking, and registration. Neither is a HOL rule. Rule costs include their
typing and cleanup work, but exclude recursively reconstructed dependencies.

Exception counts count throwing frames, not distinct failing trace steps: an
exception can propagate through several rules. Failed attempts are included.
Counters retain no terms or proofs and reset after each named theorem.

Detailed measurement adds per-step clock/counter overhead, so compare timings
under the same settings. Without a CSV path, only theorem-boundary resource
samples and cache-hit counting remain enabled.
