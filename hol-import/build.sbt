val scala3Version = "3.8.1"

lazy val root = project
  .in(file("."))
  .settings(
    name := "hol-import",
    version := "0.1.0-SNAPSHOT",

    scalaVersion := scala3Version,

    libraryDependencies += "org.scalameta" %% "munit" % "1.0.0" % Test,
    libraryDependencies += "com.lihaoyi" %% "upickle" % "4.4.3",
    libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.4.0"
  )
