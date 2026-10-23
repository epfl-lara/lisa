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

val scala3 = "3.8.4"
val commonSettings = Seq(
  crossScalaVersions := Seq(scala3),
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
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.19" % "test",
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

lazy val kernel = Project(
  id = "lisa-kernel",
  base = file("lisa-kernel")
)
  .settings(commonSettings)
  .settings(
    scalaVersion := scala3,
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.19" % "test"
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
    Compile / unmanagedSources := {
      val src = (Compile / scalaSource).value
      (src ** "*.scala").get().filter { file =>
        val path = IO.relativize(src, file).getOrElse("")
        path == "lisa/Main.scala" ||
        path == "lisa/SetTheoryLibrary.scala" ||
        path.startsWith("lisa/maths/")
      }
    },
    Test / unmanagedSources := {
      val src = (Test / scalaSource).value
      (src ** "*.scala").get().filter { file =>
        val path = IO.relativize(src, file).getOrElse("")
        path.startsWith("lisa/maths/")
      }
    }
  )
  .dependsOn(kernel, utils)

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
      libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.4.0" % Test
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
