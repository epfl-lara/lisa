version := "0.9.4"
homepage := Some(uri("https://github.com/epfl-lara/lisa"))
startYear := Some(2021)
organization := "ch.epfl.lara"
organizationName := "LARA"
organizationHomepage := Some(uri("https://lara.epfl.ch"))
licenses := Seq("Apache-2.0" -> uri("https://www.apache.org/licenses/LICENSE-2.0.html"))
versionScheme := Some("semver-spec")
scalacOptions ++= Seq(
  "-feature",
  "-deprecation",
  "-unchecked"
)
javacOptions ++= Seq("-encoding", "UTF-8")
semanticdbEnabled := true
semanticdbVersion := "4.17.4"

val scala3 = "3.10.1"

val commonSettings = Seq(
  crossScalaVersions := Seq(scala3),
  // scalacOptions += "-Wsafe-init",
  run / fork := true
)

val commonSettings3 = commonSettings ++ Seq(
  scalaVersion := scala3,
  scalacOptions ++= Seq(
    "-language:implicitConversions",
    "-Wconf:msg=.*is not declared infix*:silent",
    "-Wconf:msg=.*trait or object is defined in the compilation unit.*:silent",
    "-language:experimental.modularity"
  ),
  javaOptions += "-Xmx10G",
  javaOptions += "-Dfile.encoding=UTF-8",
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.20" % "test",
  libraryDependencies += "com.lihaoyi" %% "sourcecode" % "0.4.4",
  Test / parallelExecution := false,
  Test / fork := true
)

def withTests(project: Project): ClasspathDependency =
  project % "compile->compile;test->test"

lazy val root = Project(
  id = "lisa",
  base = file(".")
)
  .settings(commonSettings3)
  .dependsOn(kernel, utils, sets)
  .aggregate(utils, sets)

LocalRootProject / Compile / run := (sets / Compile / run).evaluated

lazy val runAll = taskKey[Unit]("Run all mathematical developments in name order.")

runAll / aggregate := false
runAll := Def.uncached {
  // Command-line tools outside lisa.maths require arguments.
  val mains = (sets / Compile / discoveredMainClasses).value.filter(_.startsWith("lisa.maths.")).sorted
  val converter = fileConverter.value
  val classpath = (sets / Compile / fullClasspath).value.map(entry => converter.toPath(entry.data))
  val mainRunner = (sets / Compile / run / runner).value
  val log = streams.value.log
  require(mains.nonEmpty, "No main classes discovered")
  log.info(s"Running ${mains.size} main classes")
  mains.foreach(main => mainRunner.run(main, classpath, Nil, log).get)
}

lazy val kernel = Project(
  id = "lisa-kernel",
  base = file("lisa-kernel")
)
  .settings(commonSettings)
  .settings(
    scalaVersion := scala3,
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.20" % "test"
  )

lazy val utils = Project(
  id = "lisa-utils",
  base = file("lisa-utils")
)
  .settings(commonSettings3)
  .dependsOn(kernel)

lazy val sets = Project(
  id = "lisa-sets",
  base = file("lisa-sets")
)
  .settings(commonSettings3)
  .settings(
    resolvers += "jitpack" at "https://jitpack.io",
    libraryDependencies ++= Seq(
      "org.apache.commons" % "commons-math3" % "3.6.1",
      "it.unimi.dsi" % "fastutil-core" % "8.5.19",
      "com.github.SC-TPTP" % "scala-tptp-parser_2.13" % "0b4ffa55c71415e925080608707c78ada1d750e5"
    )
  )
  .dependsOn(kernel, withTests(utils))

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
  .settings(commonSettings)
  .settings(commonSettings3)
  .dependsOn(root)

lazy val holImport = Project(
  id = "lisa-hol",
  base = file("lisa-hol")
)
  .settings(
    commonSettings3 ++ Seq(
      libraryDependencies += "com.lihaoyi" %% "upickle" % "4.4.3",
      libraryDependencies += "com.lihaoyi" %% "fastparse" % "3.1.1",
      libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.5.0" % Test
    )
  )
  .dependsOn(sets, utils)

lazy val coc = Project(
  id = "lisa-coc",
  base = file("lisa-coc")
)
  .settings(commonSettings)
  .settings(commonSettings3)
  .dependsOn(root)
