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

val scala2 = "2.13.8"
val scala3 = "3.2.1-RC1-bin-20220619-4cb967f-NIGHTLY"

val commonSettings2 = Seq(
  scalaVersion := scala2
)
val commonSettings3 = Seq(
  scalaVersion := scala3,
  scalacOptions ++= Seq(
    "-language:implicitConversions",

    // "-source:future", re-enable when liancheng/scalafix-organize-imports#221 is fixed
    "-old-syntax",
    "-no-indent"

  ),
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % "test",
  libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.1",
  Test / parallelExecution := false
)

def withTests(project: Project): ClasspathDependency =
  project % "compile->compile;test->test"

def githubProject(repo: String, commitHash: String) = RootProject(uri(s"$repo#$commitHash"))

lazy val scallion = githubProject("https://github.com/epfl-lara/scallion.git", "08b333f9af2d8daa1fb7424cd47b0433cd5e9770")
lazy val silex = githubProject("https://github.com/epfl-lara/silex.git", "eaf296425b9d8cc9100dfa66a079641ee4cfe4ae")

lazy val root = Project(
  id = "lisa",
  base = file(".")
)
  .settings(commonSettings3)
  .settings(
    version := "0.1"
  )
  .dependsOn(kernel, withTests(utils), theories, tptp, front) // Everything but `examples`
  .aggregate(kernel, utils, theories, tptp, front) // To run tests on all modules

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

lazy val theories = Project(
  id = "lisa-theories",
  base = file("lisa-theories")
)
  .settings(commonSettings3)
  .dependsOn(withTests(utils))

lazy val tptp = Project(
  id = "lisa-tptp",
  base = file("lisa-tptp")
)
  .settings(commonSettings3)
  .settings(
    libraryDependencies += "io.github.leoprover" % "scala-tptp-parser_2.13" % "1.4"
  )
  .dependsOn(withTests(utils))

lazy val front = Project(
  id = "lisa-front",
  base = file("lisa-front"),
)
    .settings(commonSettings3)
    .dependsOn(kernel, utils, theories)


lazy val examples = Project(
  id = "lisa-examples",
  base = file("lisa-examples")
)
  .settings(commonSettings3)
  .dependsOn(root)
