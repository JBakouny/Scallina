
organization := "scala.of.coq"

name := "scallina"

version := "0.7"

scalaVersion := "2.13.0"

libraryDependencies ++= Seq(
  "org.scalactic" %% "scalactic" % "3.0.8",
  "org.scalatest" %% "scalatest" % "3.0.8" % "test",
  "org.scala-lang.modules"  %% "scala-parser-combinators" % "1.1.2"
)

libraryDependencies += "junit" % "junit" % "4.12" % "test"

libraryDependencies += "com.eed3si9n" %% "treehugger" % "0.4.4"

resolvers += Resolver.sonatypeRepo("public")

EclipseKeys.withSource := true

