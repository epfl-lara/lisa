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

def withTests(project: Project): ClasspathDependency =
  project % "compile->compile;test->test"

def githubProject(repo: String, commitHash: String) = RootProject(uri(s"$repo#$commitHash"))

// lazy val scallion = githubProject("https://github.com/epfl-lara/scallion.git", "08b333f9af2d8daa1fb7424cd47b0433cd5e9770")
// lazy val silex = githubProject("https://github.com/epfl-lara/silex.git", "eaf296425b9d8cc9100dfa66a079641ee4cfe4ae")

val commonSettings = Seq(
  version            := "0.6",
  scalaVersion       := "3.2.0",
  crossScalaVersions := Seq("2.12.13", "2.13.4", "3.0.1", "3.2.0"),
  organization       := "ch.epfl.lara",
  scalacOptions     ++= Seq("-Ximport-suggestion-timeout", "0")
)

lazy val silex = project
  .in(file("./silex/"))
  .settings(
    commonSettings,
    name               := "silex",

    scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
      "-unchecked"
    ),

    Compile / doc / scalacOptions ++= Seq(
      "-groups",
      "-sourcepath", baseDirectory.value.getAbsolutePath,
      "-doc-source-url", "https://raw.githubusercontent.com/epfl-lara/silex/master€{FILE_PATH}.scala",
      "-doc-root-content", baseDirectory.value + "/project/root-doc.txt"
    ),

    Compile / doc / target := baseDirectory.value / "docs",

    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.2.9" % Test,
    ),

//    bintrayOrganization := Some("epfl-lara"),
//    licenses += ("Apache-2.0", url("https://opensource.org/licenses/Apache-2.0")),
//    bintrayPackageLabels := Seq(
//      "scala", "lexer", "lexing"
//    ),
  )

lazy val scallion = project
  .in(file("./scallion/"))
  .settings(
    commonSettings,
    name := "scallion",

    scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
      "-unchecked"
    ),

    Compile / doc / scalacOptions ++= Seq(
      "-groups",
      "-sourcepath", baseDirectory.value.getAbsolutePath,
      "-doc-source-url", "https://raw.githubusercontent.com/epfl-lara/scallion/master€{FILE_PATH}.scala",
      "-doc-root-content", baseDirectory.value + "/project/root-doc.txt"
    ),

    Compile / doc / target := baseDirectory.value / "docs",

    libraryDependencies ++= Seq(
      "org.scalatest" %% "scalatest" % "3.2.9" % "test",
    ),

    licenses += ("Apache-2.0", url("https://opensource.org/licenses/Apache-2.0")),
  )
  .dependsOn(silex)

//

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
    "-old-syntax",
    "-no-indent"

  ),
  libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % "test",
  libraryDependencies += "com.lihaoyi" %% "sourcecode" % "0.3.0",
  libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.1",
  Test / parallelExecution := false
)

lazy val root = Project(
    id = "lisa",
    base = file(".")
  )
  .settings(commonSettings3)
  .settings(
    version := "0.1"
  )
  .dependsOn(kernel, withTests(utils)) // Everything but `examples`
  .aggregate(kernel, utils) // To run tests on all modules

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




lazy val examples = Project(
  id = "lisa-examples",
  base = file("lisa-examples")
)
  .settings(commonSettings)
  .settings(commonSettings3)
  .dependsOn(root)