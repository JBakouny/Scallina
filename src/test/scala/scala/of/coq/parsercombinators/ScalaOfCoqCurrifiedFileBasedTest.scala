package scala.of.coq.parsercombinators

import java.io.File
import java.net.URL

import org.scalatest.FunSuite

import scala.of.coq.parsercombinators.TestUtils._
import scala.of.coq.parsercombinators.compiler.{Currify, ScalaOfCoq}
import scala.of.coq.parsercombinators.parser.CoqParser

class ScalaOfCoqCurrifiedFileBasedTest extends FunSuite {

  def fileToString(directory: String, extension: String)(fileName: String): String = {
    val fileBufferedSource = io.Source.fromURL(getClass.getResource(directory + "/" + fileName + "." + extension))
    try fileBufferedSource.mkString
    finally fileBufferedSource.close()
  }

  def actualScalaCode(fileName: String): String = {
    val coqAST = CoqParser(fileToString("", "v")(fileName))

    val optionalCoqAst = Option(coqAST.getOrElse(null))

    val outputString = optionalCoqAst.fold(coqAST.toString) { coqTrees ⇒
      new ScalaOfCoq(coqTrees, Currify).createObjectFileCode(fileName)
    }

    normalizeWhitespace(outputString)
  }

  def expectedScalaCode(fileName: String): String = {
    val fileStringContents =
      fileToString("/scala/of/coq/generated/code", "scala")(fileName)

    normalizeWhitespace("package .+".r.replaceAllIn(fileStringContents, _ ⇒ ""))
  }

  def getListOfFiles(dir: URL): List[String] = {
    val d = new File(dir.getPath)
    if (d.exists && d.isDirectory) {
      d.listFiles.filter(_.isFile).map(_.getName).toList
    } else {
      List[String]()
    }
  }

  test("""Testing all Coq file conversions to Scala """) {

    val allCoqFileNames =
      getListOfFiles(getClass.getResource("/")).filter(_.endsWith(".v"))
    val allBaseNamesWithoutExtension =
      allCoqFileNames.map(fileName ⇒ """(.*/)?([^/]+)\.v$""".r.replaceFirstIn(fileName, "$2"))

    for (name ← allBaseNamesWithoutExtension) {
      info("Testing " + name)
      assert(actualScalaCode(name) === expectedScalaCode(name))
    }

  }

}
