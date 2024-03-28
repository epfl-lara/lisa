# ITP 2024 Archive

This branch is an archive containing the implementation of the features presented in the paper submitted at ITP 2024.

## Installation and utilisation

 - First, [install Scala 3 on your system per the official
   instructions](https://www.scala-lang.org/download/). You should have obtained
   Scala 3 and [SBT](https://www.scala-sbt.org/).
 - Then, clone the present project.
 - In the root folder, run `sbt`.
 - Type `project lisa-examples` in the `sbt` interactive console.
 - Then `run`
    - For examples of typechecking proofs within Lisa, select `HOLTypechecking` as the main class (number 4).
    - For an example of ADT definition and typecheking within Lisa, select `ADT` as the main class (number 1).
    - For an example of automatic import of a part of HOL Light library in Lisa, select `HOLImport` as the main class (number 2).

- All examples are implemented in [Example.scala](https://github.com/epfl-lara/lisa/blob/itp2024-archive/lisa-sets/src/main/scala/lisa/hol/Example.scala) .
