# Beginning Contributing Guide

First, learn about infinity, consulting:
  * https://link.springer.com/book/10.1007/3-540-44761-X 
  * https://www.youtube.com/watch?v=DsyJNmOXtmc 

## System Prerequisites

- JDK 17 or later (the CI runs on Java 17).
- Scala 3 and `sbt` installed.
- A local clone of the repository.

## Getting Started Locally

From the repository root:

```bash
sbt
```

Useful commands in `sbt`:

- `compile`: compile the default project.
- `test`: run test suites.
- `scalafmtAll`: format Scala sources.
- `scalafixAll`: apply linting and rewrites.
- `run`: run a main entry point (prompts for which one).

Examples:

```bash
sbt compile
sbt test
sbt scalafmtAll
sbt scalafixAll
```

## Project Structure

- `lisa-kernel`: trusted logical kernel.
- `lisa-utils`: utilities and proof DSL on top of the kernel.
- `lisa-sets`: set-theory developments and related proofs.
- `lisa-examples`: examples and executable demonstrations.
- `lisa-coc`: additional project module in this repository.

When possible, keep changes scoped to the smallest relevant module.

## Style and Quality Checks

Before opening a pull request, run checks locally:

```bash
sbt compile
sbt test
sbt "scalafixAll --check"
sbt scalafmtCheckAll
```

These commands mirror CI expectations.

Formatting is configured in `.scalafmt.conf` (Scala 3 dialect).

## Tests

- Add or update tests whenever behavior changes.
- Keep tests close to the module you changed (`lisa-utils/src/test`, `lisa-sets/src/test`, etc.).
- Ensure `sbt test` passes before submitting.

## Pull Requests

- Write a clear title and description.
- Explain what changed and why.
- Link related issues when relevant.
- Keep PRs focused; smaller PRs are easier to review.

## Reference Material

- Main documentation: `README.md`
- Reference manual: `refman/lisa.pdf`

If you are unsure where a contribution should go, open a draft PR or issue and ask for guidance.