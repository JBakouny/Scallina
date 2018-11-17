
organization := "scala.of.coq"

name := "scallina"

version := "0.6-SNAPSHOT"

scalaVersion := "2.12.7"

libraryDependencies ++= Seq(
  "org.scalatest"           %% "scalatest"                % "3.0.5" % "test",
  "org.scala-lang.modules"  %% "scala-parser-combinators" % "1.1.1"
)

libraryDependencies += "junit" % "junit" % "4.12" % "test"

libraryDependencies += "com.eed3si9n" %% "treehugger" % "0.4.3"


