ThisBuild / version := "0.6"
ThisBuild / homepage := Some(url("https://github.com/epfl-lara/lisa"))
ThisBuild / startYear := Some(2021)
ThisBuild / organization := "ch.epfl.lara"
ThisBuild / organizationName := "LARA"
ThisBuild / organizationHomepage := Some(url("https://lara.epfl.ch"))
ThisBuild / licenses := Seq("Apache-2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0.html"))
ThisBuild / versionScheme := Some("semver-spec")
ThisBuild / scalacOptions ++= Seq(
  "-feature",
  "-deprecation",
  "-unchecked"
)
ThisBuild / javacOptions ++= Seq("-encoding", "UTF-8")
ThisBuild / semanticdbEnabled := true
ThisBuild / semanticdbVersion := scalafixSemanticdb.revision
ThisBuild / scalafixDependencies += "com.github.liancheng" %% "organize-imports" % "0.6.0"




val commonSettings = Seq(
  crossScalaVersions := Seq("2.12.13", "2.13.4", "3.0.1", "3.2.0"),
  run / fork := true
)

val scala2 = "2.13.8"
val scala3 = "3.3.1"

val commonSettings2 = commonSettings ++ Seq(
  scalaVersion := scala2,
  scalacOptions ++= Seq("-Ypatmat-exhaust-depth", "50")
)
val commonSettings3 = commonSettings ++ Seq(
  scalaVersion := scala3,
  scalacOptions ++= Seq(
    "-language:implicitConversions"

    // "-source:future", re-enable when liancheng/scalafix-organize-imports#221 is fixed

  ),
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % "test",
  libraryDependencies += "com.lihaoyi" %% "sourcecode" % "0.3.0",
  // libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.1",
  libraryDependencies += ("io.github.uuverifiers" %% "princess" % "2023-06-19").cross(CrossVersion.for3Use2_13),
  Test / parallelExecution := false
)

def withTests(project: Project): ClasspathDependency =
  project % "compile->compile;test->test"

def githubProject(repo: String, commitHash: String) = RootProject(uri(s"$repo#$commitHash"))

lazy val scallion = githubProject("https://github.com/sankalpgambhir/scallion.git", "6434e21bd08872cf547c8f0efb67c963bfdf4190")

lazy val silex = githubProject("https://github.com/epfl-lara/silex.git", "fc07a8670a5fa8ea2dd5649a00424710274a5d18")

scallion / scalacOptions ~= (_.filterNot(Set("-Wvalue-discard")))
silex / scalacOptions ~= (_.filterNot(Set("-Wvalue-discard")))

lazy val root = Project(
  id = "lisa",
  base = file(".")
)
  .settings(commonSettings3)
  .dependsOn(kernel, withTests(utils), withTests(sets)) // Everything but `examples`
  .aggregate(utils) // To run tests on all modules

lazy val kernel = Project(
  id = "lisa-kernel",
  base = file("lisa-kernel")
)
  .settings(commonSettings2)
  .settings(
    crossScalaVersions := Seq(scala3)
  )

lazy val sets = Project(
  id = "lisa-sets",
  base = file("lisa-sets")
)
  .settings(commonSettings3)
  .dependsOn(kernel, withTests(utils))

lazy val utils = Project(
  id = "lisa-utils",
  base = file("lisa-utils")
)
  .settings(commonSettings3)
  .dependsOn(kernel)
  .dependsOn(silex)
  .dependsOn(scallion % "compile->compile")
  .settings(libraryDependencies += "io.github.leoprover" % "scala-tptp-parser_2.13" % "1.4")

ThisBuild / assemblyMergeStrategy := {
  case PathList("module-info.class") => MergeStrategy.discard
  case x if x.endsWith("/module-info.class") => MergeStrategy.discard
  case x if x.endsWith(".class") => MergeStrategy.first
  case x if x.endsWith(".tasty") => MergeStrategy.first
  case x =>
    val oldStrategy = (ThisBuild / assemblyMergeStrategy).value
    oldStrategy(x)
}


lazy val examples = Project(
  id = "lisa-examples",
  base = file("lisa-examples")
)
  .settings(commonSettings)
  .settings(commonSettings3)
  .dependsOn(root)
