
organization := "scala.of.coq"

name := "scallina"

version := "0.8-SNAPSHOT"

scalaVersion := "3.8.1"

libraryDependencies ++= Seq(
  "org.scalactic"            %% "scalactic"                % "3.2.19",
  "org.scalatest"            %% "scalatest"                % "3.2.19" % "test",
  "org.scala-lang.modules"   %% "scala-parser-combinators" % "2.4.0",
  "junit"                     % "junit"                    % "4.13.2" % "test",
  ("com.eed3si9n"            %% "treehugger"               % "0.4.4").cross(CrossVersion.for3Use2_13)
)

