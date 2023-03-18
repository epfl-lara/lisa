# LISA = LISA Is Sets Automated

LISA is a Proof Assistant based on first order logic, sequent calculus and set theory. To get started, look at the [Reference Manual](Reference%20Manual/lisa.pdf).

EPFL-LARA Website: https://lara.epfl.ch/w/

## Installation and utilisation
 - You first need to [install Scala on your system](https://www.scala-lang.org/download/).
 - Then, clone the presen project.
 - In the root folder, type `sbt`.
 - To execute a file in LISA's Mathematical Library, type `run` and select a file (try with `SetTheory.scala` first!). SBT will install missing packages and compile the project, and output the theorems of the file.
 - To experiment with the system, type `project lisa-examples`.
 - We recommand using VSCode or Intelliji to edit lisa code. Create a new file in the lisa-examples folder. You can use the file `Examples.scala` as a template.


## Project Organisation

### Kernel
The kernel package contains the trusted code of LISA, in the sense that it only can produce theorem and verify proof. Any bug or error in code written outside this package should not possibly break soundness.
The kernel contains essentially two elements: Formalisation of First Order Logic, and Formalisation of Proofs through Sequent Calculus.

### Utils
The utils package contains a set of utilities to interract with the kernel. Syntactic sugar, a parser and printer for proofs and formulas, interraction with tptp library, unification algorithms. The package also contains LISA's DSL to write proofs, tactics and mathematical developments.

## Commands

* `sbt test` to compile and execute the test suite
* `sbt assembly` to package it as a library
* `sbt doc` to generate the Scala documentation
* `sbt run` to execute a LISA file
* `sbt scalafix` to lint the whole codebase
* `sbt scalafmt` to format the whole codebase

## LICENSE
   Copyright 2023 EPFL

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
