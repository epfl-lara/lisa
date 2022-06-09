name := "lisa"
organization := "ch.epfl.lara"
licenses := Seq("Apache-2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0.html"))

version := "0.1"

scalaVersion := "3.0.2"

scalacOptions ++= Seq("-deprecation", "-feature")
scalacOptions ++= Seq(
  "-language:implicitConversions"
)

libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % "test"
libraryDependencies += "io.github.leoprover" % "scala-tptp-parser_2.13" % "1.4"
Test / parallelExecution := false

ThisBuild / semanticdbEnabled := true
ThisBuild / semanticdbVersion := scalafixSemanticdb.revision
ThisBuild / scalafixDependencies += "com.github.liancheng" %% "organize-imports" % "0.6.0"