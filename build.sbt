inThisBuild(
  Def.settings(
    organization := "ch.epfl.lara",
    organizationName := "LARA",
    organizationHomepage := Some(url("https://lara.epfl.ch")),
    licenses := Seq("Apache-2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0.html")),
    versionScheme := Some("semver-spec"),
    scalacOptions ++= Seq(
      "-feature",
      "-deprecation",
      "-unchecked"
    ),
    javacOptions ++= Seq("-encoding", "UTF-8"),
    semanticdbEnabled := true,
    semanticdbVersion := scalafixSemanticdb.revision,
    scalafixDependencies += "com.github.liancheng" %% "organize-imports" % "0.6.0"
  )
)


val commonSettings = Seq(
  version            := "0.6",
  crossScalaVersions := Seq("2.12.13", "2.13.4", "3.0.1", "3.2.0"),
  organization       := "ch.epfl.lara",
  scalacOptions     ++= Seq("-Ximport-suggestion-timeout", "0"),
  run / fork := true
)


val scala2 = "2.13.8"
val scala3 = "3.2.2"

fork := true

val commonSettings2 = Seq(
  scalaVersion := scala2,
  scalacOptions ++= Seq("-Ypatmat-exhaust-depth", "50")
)
val commonSettings3 = Seq(
  scalaVersion := scala3,
  scalacOptions ++= Seq(
    "-language:implicitConversions",

    // "-source:future", re-enable when liancheng/scalafix-organize-imports#221 is fixed

  ),
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % "test",
  libraryDependencies += "com.lihaoyi" %% "sourcecode" % "0.3.0",
  //libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.1",
  libraryDependencies += ("io.github.uuverifiers" %% "princess" % "2023-06-19").cross(CrossVersion.for3Use2_13),
  Test / parallelExecution := false
)

def withTests(project: Project): ClasspathDependency =
  project % "compile->compile;test->test"

def githubProject(repo: String, commitHash: String) = RootProject(uri(s"$repo#$commitHash"))

lazy val scallion = githubProject("https://github.com/sankalpgambhir/scallion.git", "6434e21bd08872cf547c8f0efb67c963bfdf4190")
lazy val silex = githubProject("https://github.com/epfl-lara/silex.git", "fc07a8670a5fa8ea2dd5649a00424710274a5d18")
// lazy val princess = RootProject(file("../princess")) // If you have a local copy of Princess and would like to do some changes
//lazy val princess = githubProject("https://github.com/uuverifiers/princess.git", "93cbff11d7b02903e532c7b64207bc12f19b79c7")

lazy val root = Project(
    id = "lisa",
    base = file(".")
  )
  .settings(commonSettings3)
  .settings(
    version := "0.1"
  )
  .dependsOn(kernel, withTests(utils)) // Everything but `examples`
  .aggregate(utils) // To run tests on all modules

lazy val kernel = Project(
  id = "lisa-kernel",
  base = file("lisa-kernel")
)
  .settings(commonSettings2)
  .settings(
    crossScalaVersions := Seq(scala3)
  )

lazy val utils = Project(
  id = "lisa-utils",
  base = file("lisa-utils")
)

  .settings(commonSettings3)
  .dependsOn(kernel)
  .dependsOn(silex)
  .dependsOn(scallion % "compile->compile")
  .settings(libraryDependencies += "io.github.leoprover" % "scala-tptp-parser_2.13" % "1.4")

lazy val lab05 = Project(
  id = "fv-lab05",
  base = file("fv-lab05")
)
  .settings(commonSettings)
  .settings(commonSettings3)
  .dependsOn(root)


lazy val examples = Project(
  id = "lisa-examples",
  base = file("lisa-examples")
)
  .settings(commonSettings)
  .settings(commonSettings3)
  .dependsOn(root)