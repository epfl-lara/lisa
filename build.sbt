version := "0.9.4"
homepage := Some(url("https://github.com/epfl-lara/lisa"))
startYear := Some(2021)
organization := "ch.epfl.lara"
organizationName := "LARA"
organizationHomepage := Some(url("https://lara.epfl.ch"))
licenses := Seq("Apache-2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0.html"))
versionScheme := Some("semver-spec")
scalacOptions ++= Seq(
  "-feature",
  "-deprecation",
  "-unchecked"
)
javacOptions ++= Seq("-encoding", "UTF-8")
semanticdbEnabled := true
semanticdbVersion := "4.13.6"
exportJars := false
resolvers += "jitpack" at "https://jitpack.io"

val scala2Version = "2.13.16"
val scala3Version = "3.8.4"
val scalaTestVersion = "3.2.19"
val tptpParserCommit = "0b4ffa55c71415e925080608707c78ada1d750e5"

val commonProjectSettings = Seq(
  run / fork := true
)

val scala3ProjectSettings = Seq(
  scalaVersion := scala3Version,
  scalacOptions ++= Seq(
    "-language:implicitConversions",
    "-Wconf:msg=.*is not declared infix*:silent",
    "-Wconf:msg=.*trait or object is defined in the compilation unit.*:silent",
    "-language:experimental.modularity"
  ),
  javaOptions += "-Xmx10G",
  libraryDependencies ++= Seq(
    "org.scalatest" %% "scalatest" % scalaTestVersion % Test,
    "com.lihaoyi" %% "sourcecode" % "0.4.4"
  ),
  Test / parallelExecution := false,
  Test / fork := true
)

val allowScala2ProjectDependency = Seq(
  allowMismatchScala := true
)

def withTests(project: Project): ClasspathDependency =
  project % "compile->compile;test->test"

lazy val root = Project(
  id = "lisa",
  base = file(".")
)
  .settings(commonProjectSettings)
  .settings(scala3ProjectSettings)
  .settings(allowScala2ProjectDependency)
  .dependsOn(kernel, withTests(utils), withTests(sets)) // Everything but `examples`
  .aggregate(utils) // To run tests on all modules

LocalRootProject / Compile / run := (sets / Compile / run).evaluated

lazy val kernel = Project(
  id = "lisa-kernel",
  base = file("lisa-kernel")
)
  .settings(commonProjectSettings)
  .settings(
    scalaVersion := scala2Version,
    crossScalaVersions := Seq(scala3Version),
    scalacOptions ++= Seq("-Ypatmat-exhaust-depth", "50"),
    libraryDependencies += "org.scalatest" %% "scalatest" % scalaTestVersion % Test
  )

lazy val sets = Project(
  id = "lisa-sets",
  base = file("lisa-sets")
)
  .settings(commonProjectSettings)
  .settings(scala3ProjectSettings)
  .settings(allowScala2ProjectDependency)
  .dependsOn(kernel, withTests(utils))

lazy val utils = Project(
  id = "lisa-utils",
  base = file("lisa-utils")
)
  .settings(commonProjectSettings)
  .settings(scala3ProjectSettings)
  .settings(allowScala2ProjectDependency)
  .settings(
    libraryDependencies ++= Seq(
      "com.lihaoyi" %% "mainargs" % "0.7.6",
      "com.github.SC-TPTP" % "scala-tptp-parser_2.13" % tptpParserCommit
    )
  )
  .dependsOn(kernel)

assemblyMergeStrategy := {
  case PathList("module-info.class") => MergeStrategy.discard
  case x if x.endsWith("/module-info.class") => MergeStrategy.discard
  case x if x.endsWith(".class") => MergeStrategy.first
  case x if x.endsWith(".tasty") => MergeStrategy.first
  case x =>
    val oldStrategy = assemblyMergeStrategy.value
    oldStrategy(x)
}

lazy val examples = Project(
  id = "lisa-examples",
  base = file("lisa-examples")
)
  .settings(commonProjectSettings)
  .settings(scala3ProjectSettings)
  .dependsOn(root)

lazy val coc = Project(
  id = "lisa-coc",
  base = file("lisa-coc")
)
  .settings(commonProjectSettings)
  .settings(scala3ProjectSettings)
  .dependsOn(root)
