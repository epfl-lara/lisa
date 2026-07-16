ThisBuild / version := "0.9.3"
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
  scalacOptions ++= Seq("-Ypatmat-exhaust-depth", "50"),
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.19" % "test",
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
  .dependsOn(kernelcf, utilcfs, setslcf)
  .aggregate(utilcfs, setslcf)

Compile / run := (setslcf / Compile / run).evaluated

lazy val kernel = Project(
  id = "lisa-kernel",
  base = file("lisa-kernel")
)
  .settings(commonSettings2)
  .settings(
    crossScalaVersions := Seq(scala3)
  )

lazy val kernelcf = Project(
  id = "lisa-kernelcf",
  base = file("lisa-kernelcf")
)
  .settings(commonSettings)
  .settings(
    scalaVersion := scala3,
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.19" % "test"
  )

lazy val utilcfs = Project(
  id = "lisa-utilcfs",
  base = file("lisa-utilcfs")
)
  .settings(commonSettings3)
  .dependsOn(kernelcf)

lazy val setslcf = Project(
  id = "lisa-setslcf",
  base = file("lisa-setslcf")
)
  .settings(commonSettings3)
  .settings(
    Compile / unmanagedSources := {
      val src = (Compile / scalaSource).value
      (src ** "*.scala").get.filter { file =>
        val path = IO.relativize(src, file).getOrElse("")
        path == "lisa/Main.scala" ||
        path == "lisa/SetTheoryLibrary.scala" ||
        path.startsWith("lisa/maths/")
      }
    }
  )
  .dependsOn(kernelcf, utilcfs)

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

lazy val coc = Project(
  id = "lisa-coc",
  base = file("lisa-coc")
)
  .settings(commonSettings)
  .settings(commonSettings3)
  .dependsOn(root)
