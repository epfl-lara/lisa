#LISA: LISA Is Sets Automated


## Kernel
The kernel package contains the trusted code of LISA, in the sense that it only can produce theorem and verify proof. Any bug or error in code written outside this package should not possibly break soundness.
The kernel contains essentially two elements: Formalisation of First Order Logic, and Formalisation of Proofs through Sequent Calculus.

## Proven
The proven package contains tactics and proofs

## TPTP
The TPTP package contains a parser from the TPTP file format to LISA. The simplest way to use it is to download the TPTP library and put it inside main/resources.

## Commands

* `sbt test` to compile and execute the test suite
* `sbt assembly` to package it as a library
* `sbt doc` to generate the Scala documentation
