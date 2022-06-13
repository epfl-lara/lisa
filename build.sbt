inThisBuild(Def.settings(
  organization := "ch.epfl.lara",
  organizationName := "LARA",
  organizationHomepage := Some(url("https://lara.epfl.ch")),
  licenses := Seq("Apache-2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0.html")),
  versionScheme := Some("semver-spec"),
))

val scala2 = "2.13.8"
val scala3 = "3.1.3"

lazy val commonSettings2 = Seq(
  scalaVersion := scala2,
)
lazy val commonSettings3 = Seq(
  scalaVersion := scala3,
  scalacOptions ++= Seq(
    "-feature",
    "-deprecation",
    //"-source:future",
    "-language:implicitConversions",
    //"-old-syntax",
    //"-no-indent",
  ),
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % "test",
  Test / parallelExecution := false,
  semanticdbEnabled := true,
  semanticdbVersion := scalafixSemanticdb.revision,
  scalafixDependencies += "com.github.liancheng" %% "organize-imports" % "0.6.0",
)

lazy val root = Project(
  id = "lisa-core",
  base = file("."),
)
  .settings(commonSettings3)
  .settings(
    version := "0.1",
  )
  .dependsOn(kernel, utils, theories, tptp) // Everything but `examples`

lazy val kernel = Project(
  id = "lisa-kernel",
  base = file("lisa-kernel"),
)
  .settings(commonSettings2)
  .settings(
    crossScalaVersions := Seq(scala3)
  )

lazy val utils = Project(
  id = "lisa-utils",
  base = file("lisa-utils"),
)
  .settings(commonSettings3)
  .dependsOn(kernel)

lazy val theories = Project(
  id = "lisa-theories",
  base = file("lisa-theories"),
)
  .settings(commonSettings3)
  .dependsOn(utils)

lazy val tptp = Project(
  id = "lisa-tptp",
  base = file("lisa-tptp"),
)
  .settings(commonSettings3)
  .settings(
    libraryDependencies += "io.github.leoprover" % "scala-tptp-parser_2.13" % "1.4",
  )
  .dependsOn(utils)

lazy val examples = Project(
  id = "lisa-examples",
  base = file("lisa-examples"),
)
  .settings(commonSettings3)
  .dependsOn(root)
