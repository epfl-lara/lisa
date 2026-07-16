# CLAUDE.md

## Project

A superposition-based theorem prover for clausal-form problems, built for Lisa in Scala.
Goals: highly efficient, low-level, with **full proof reconstruction** into the Lisa kernel.
Roadmap and phases: [PLAN.md](lisa-sets/src/main/scala/lisa/automation/superposition/PLAN.md).
Phases are done one at a time: never start a phase until the previous one is fully complete and tested, and until the user explicitly asks to start the next phase.

## Scope of work — STRICT

You are **only ever allowed to create or modify files in**:

- `lisa-sets/src/main/scala/lisa/automation/superposition/`
- `lisa-sets/src/main/scala/lisa/automation/clausification/`
- `lisa-sets/src/test/scala/lisa/automation/superposition/`
- `lisa-sets/src/test/scala/lisa/automation/clausification/`

Do **not** edit any file outside these two directories (including `build.sbt`, the
kernel, other automation, or the reference repos below). If a change elsewhere seems
necessary, stop and ask.

## Reference provers (read-only, clones under `othersolvers/`)

- `othersolvers/vampire/` — https://github.com/vprover/vampire
- `othersolvers/eprover/` — https://github.com/eprover/eprover
- `othersolvers/prover9/` — https://github.com/ai4reason/Prover9 (LADR-2017-11A snapshot, classic source)
- `othersolvers/ladr-2026/` — https://github.com/AlgorithmicTruth/Prover9 (LADR-2026, modernized)

## Build & test

- Compile: `sbt lisa-sets/compile`
- Test: `sbt lisa-sets/test`


# IMPORTANT
When the user asks a question, answer the question and propose edits, but NEVER edit without explicit instruction to do so. A user message ending with an interrogation mark makes it forbidden to do any edit this round - only answer the question.