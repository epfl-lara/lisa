ThisBuild / version      := "0.6"
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
      "-unchecked",
    )
ThisBuild / javacOptions ++= Seq("-encoding", "UTF-8")
ThisBuild / semanticdbEnabled := true
ThisBuild / semanticdbVersion := scalafixSemanticdb.revision



val scala2 = "2.13.8"
val scala3 = "3.5.1"
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
    //"-rewrite", "-source", "3.4-migration",
    "-Wconf:msg=.*will never be selected.*:silent"
  ),
  javaOptions += "-Xmx10G",
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.18" % "test",
  libraryDependencies += "com.lihaoyi" %% "sourcecode" % "0.4.1",
  Test / parallelExecution := false
)

def withTests(project: Project): ClasspathDependency =
  project % "compile->compile;test->test"

def githubProject(repo: String, commitHash: String) = RootProject(uri(s"$repo#$commitHash"))

lazy val scallion = githubProject("https://github.com/sankalpgambhir/scallion.git", "6434e21bd08872cf547c8f0efb67c963bfdf4190")

lazy val silex = githubProject("https://github.com/epfl-lara/silex.git", "fc07a8670a5fa8ea2dd5649a00424710274a5d18")
lazy val customTstpParser = githubProject("https://github.com/SimonGuilloud/scala-tptp-parser.git", "eae9c1b7a9546f74779d77ff50fa6e8a1654cfa0")

scallion/scalacOptions ~= (_.filterNot(Set("-Wvalue-discard")))
scallion/scalacOptions += "-Wconf:any:silent"

silex/scalacOptions ~= (_.filterNot(Set("-Wvalue-discard")))

lazy val root = Project(
    id = "lisa",
    base = file("."),
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

  .settings(commonSettings3)
  .dependsOn(kernel)
  .dependsOn(silex)
  .dependsOn(scallion % "compile->compile")
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
