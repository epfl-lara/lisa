# LISA = LISA Is Sets Automated

LISA is a proof assistant based on first-order logic sequent calculus and set
theory. To get started, check the [Reference Manual](refman/lisa.pdf).

LISA is developed and maintained by the [Laboratory for Automated Reasoning and
Analysis (LARA)](https://lara.epfl.ch) at the [EPFL](https://epfl.ch).

For details regarding the design of LISA and techniques implemented here, you
can check the following publications:
 
 - Simon Guilloud, Sankalp Gambhir, and Viktor Kunčak.
   LISA - A Modern Proof System.
   In 14th International Conference on Interactive Theorem Proving
   (ITP 2023). LIPIcs, Volume 268, pp. 17:1-17:19
   https://doi.org/10.4230/LIPIcs.ITP.2023.17
 - Simon Guilloud, Sankalp Gambhir, Andrea Gilot, Viktor Kuncak:
   Mechanized HOL Reasoning in Set Theory.
   In 15th International Conference on Interactive Theorem Proving
   (ITP 2024): 18:1-18:18
 - Guilloud, S., Bucev, M., Milovančević, D., Kunčak, V. (2023). Formula
   Normalizations in Verification. In: Enea, C., Lal, A. (eds) Computer Aided
   Verification. CAV 2023. Lecture Notes in Computer Science, vol 13966.
   Springer, Cham. https://doi.org/10.1007/978-3-031-37709-9_19

## Installation and utilisation

 - First, [install Scala 3 on your system per the official
   instructions](https://www.scala-lang.org/download/). You should have obtained
   Scala 3 and [SBT](https://www.scala-sbt.org/).
 - Then, clone the present project.
 - In the root folder, run `sbt`.
 - To execute a file in LISA's Mathematical Library, type `run` in the `sbt`
   interactive console and select a main class to run when prompted (try with
   `SetTheory.scala` first!). 
 - On the first run, SBT will install missing packages and compile the project,
   and outputting the theorems proved in the chosen file.
 - To experiment with the system, type `project lisa-examples`, and play around
   with the examples in
   [lisa-examples/src/main/scala/Example.scala](lisa-examples/src/main/scala/Example.scala),
   or create your own file. You can start your own LISA file with the following
   minimal header:
   ```scala
    object MyLisaFile extends lisa.Main {
        // your proofs go here
    }
   ```
 - We recommend using [Visual Studio Code](https://code.visualstudio.com/) with
   the [Metals extension](https://scalameta.org/metals/) or [JetBrains IntelliJ
   IDEA](https://www.jetbrains.com/idea/) to edit LISA code.


## Project Organisation

### Kernel

The `lisa-kernel` package contains the trusted code of LISA, in the sense that
all theorems and proofs pass through it to be considered correct. It only can
produce theorems and verify proof. Any bug or error in code written outside this
package should not possibly break soundness. 

The kernel essentially contains two elements: formalisation of first-order
logic, and formalisation of proofs through sequent calculus.

### Utils

The `lisa-utils` package contains a set of utilities to interact with the
kernel. Syntactic sugar, a parser and printer for proofs and formulas,
unification algorithms, among others. The package also contains LISA's DSL to
write proofs, tactics, and mathematical developments.

Most user-developed tactics, syntax, and auxiliary utilities go here.

## Interacting with the project

The following commands can be used to perform different actions as configured in
the project. Each command ("`command`") can be run within the `sbt` console as
simply `command` or in batch mode from a shell session in the project directory
with `sbt command` or `sbt "command; command; ..."`.

* `run` to execute a LISA file, prompting which file to run
* `runMain classPath` to run a specific main file at `classPath` without prompt.
  * For example: `runMain lisa.mathematics.settheory.SetTheory`
* `test` to compile and execute the test suite
* `assembly` to package LISA as a library
* `doc` to generate the Scala documentation
* `scalafix` to lint the whole project
* `scalafmt` to format the whole project

## License and Distribution

   Copyright 2023 EPFL

   Licensed under the Apache License, Version 2.0 (the "License"); you may not
   use this file except in compliance with the License. You may obtain a copy of
   the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
   License for the specific language governing permissions and limitations under
   the License.
