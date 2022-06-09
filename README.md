# LISA = LISA Is Sets Automated

LISA is a Proof Assistant based on first order logic, sequent calculus and set theory. To get started, look at the [Reference Manual](/LISA%20Reference%20Manual.pdf).

EPFL-LARA Website: https://lara.epfl.ch/w/

## Project Organisation

### Kernel
The kernel package contains the trusted code of LISA, in the sense that it only can produce theorem and verify proof. Any bug or error in code written outside this package should not possibly break soundness.
The kernel contains essentially two elements: Formalisation of First Order Logic, and Formalisation of Proofs through Sequent Calculus.

### Proven
The proven package contains tactics and proofs

### TPTP
The TPTP package contains a parser from the TPTP file format to LISA. The simplest way to use it is to download the TPTP library and put it inside main/resources.

## Commands

* `sbt test` to compile and execute the test suite
* `sbt assembly` to package it as a library
* `sbt doc` to generate the Scala documentation
* `sbt scalafix` to lint the whole codebase
* `sbt scalafmt` to format the whole codebase

## LICENSE
   Copyright 2022 EPFL

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
