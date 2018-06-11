
organization := "scala.of.coq"

name := "scallina"

version := "0.5"

scalaVersion := "2.12.3"

libraryDependencies ++= Seq(
  "org.scalatest"           %% "scalatest"                % "3.0.1" % "test",
  "org.scala-lang.modules"  %% "scala-parser-combinators" % "1.0.4"
)

libraryDependencies += "junit" % "junit" % "4.12" % "test"

libraryDependencies += "com.eed3si9n" %% "treehugger" % "0.4.3"

resolvers += Resolver.sonatypeRepo("public")

EclipseKeys.withSource := true

