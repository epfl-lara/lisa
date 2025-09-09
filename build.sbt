ThisBuild / version := "0.9.2"
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
ThisBuild / semanticdbVersion := "4.13.6"

val scala2 = "2.13.16"
val scala3 = "3.7.2"
val commonSettings = Seq(
  crossScalaVersions := Seq(scala3),
  run / fork := true
)

val commonSettings2 = commonSettings ++ Seq(
  scalaVersion := scala2,
  scalacOptions ++= Seq("-Ypatmat-exhaust-depth", "50")
)
val commonSettings3 = commonSettings ++ Seq(
  scalaVersion := scala3,
  scalacOptions ++= Seq(
    "-language:implicitConversions",
    "-Wconf:msg=.*will never be selected.*:silent",
    "-language:experimental.modularity"
  ),
  javaOptions += "-Xmx10G",
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.19" % "test",
  libraryDependencies += "com.lihaoyi" %% "sourcecode" % "0.4.4",
  Test / parallelExecution := false,
  Test / fork := true
)

def withTests(project: Project): ClasspathDependency =
  project % "compile->compile;test->test"

def githubProject(repo: String, commitHash: String) = RootProject(uri(s"$repo#$commitHash"))

lazy val customTstpParser = githubProject("https://github.com/SC-TPTP/scala-tptp-parser.git", "851338c4175036279279835d9f58895aed2f37ba")

lazy val root = Project(
  id = "lisa",
  base = file(".")
)
  .settings(commonSettings3)
  .dependsOn(kernel, withTests(utils), withTests(sets)) // Everything but `examples`
  .aggregate(utils) // To run tests on all modules

Compile / run := (sets / Compile / run).evaluated

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
  .settings(
    commonSettings3 ++ Seq(
      libraryDependencies += "ch.epfl.lara" %% "scallion" % "0.6" from "https://github.com/epfl-lara/scallion/releases/download/v0.6/scallion_3-0.6.jar",
      libraryDependencies += "ch.epfl.lara" %% "silex" % "0.6" from "https://github.com/epfl-lara/silex/releases/download/v0.6/silex_3-0.6.jar",
      libraryDependencies += "com.lihaoyi" %% "mainargs" % "0.7.6"
    )
  )
  .dependsOn(kernel)
  .dependsOn(customTstpParser)
//.settings(libraryDependencies += "io.github.leoprover" % "scala-tptp-parser_2.13" % "1.4")

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
