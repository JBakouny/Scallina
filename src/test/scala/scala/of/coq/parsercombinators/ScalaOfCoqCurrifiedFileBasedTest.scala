package scala.of.coq.parsercombinators

import scala.of.coq.parsercombinators.parser.CoqTermParser
import scala.of.coq.parsercombinators.parser.Argument
import scala.of.coq.parsercombinators.parser.BetweenParenthesis
import scala.of.coq.parsercombinators.parser.Binders
import scala.of.coq.parsercombinators.parser.ConstructorPattern
import scala.of.coq.parsercombinators.parser.DepRetType
import scala.of.coq.parsercombinators.parser.ExplicitBinderWithType
import scala.of.coq.parsercombinators.parser.Fix
import scala.of.coq.parsercombinators.parser.FixBodies
import scala.of.coq.parsercombinators.parser.FixBody
import scala.of.coq.parsercombinators.parser.ForAll
import scala.of.coq.parsercombinators.parser.Fun
import scala.of.coq.parsercombinators.parser.Ident
import scala.of.coq.parsercombinators.parser.ImplicitBinder
import scala.of.coq.parsercombinators.parser.LetConstructorArgsIn
import scala.of.coq.parsercombinators.parser.LetFixIn
import scala.of.coq.parsercombinators.parser.LetPatternIn
import scala.of.coq.parsercombinators.parser.Match
import scala.of.coq.parsercombinators.parser.MatchItem
import scala.of.coq.parsercombinators.parser.MultPattern
import scala.of.coq.parsercombinators.parser.Name
import scala.of.coq.parsercombinators.parser.Number
import scala.of.coq.parsercombinators.parser.NumberPattern
import scala.of.coq.parsercombinators.parser.OrPattern
import scala.of.coq.parsercombinators.parser.ParenthesisOrPattern
import scala.of.coq.parsercombinators.parser.PatternEquation
import scala.of.coq.parsercombinators.parser.Qualid
import scala.of.coq.parsercombinators.parser.QualidPattern
import scala.of.coq.parsercombinators.parser.ReturnType
import scala.of.coq.parsercombinators.parser.ExplicitSimpleBinder
import scala.of.coq.parsercombinators.parser.SimpleLetIn
import scala.of.coq.parsercombinators.parser.TermIf
import scala.of.coq.parsercombinators.parser.{ Term_% => Term_% }
import scala.of.coq.parsercombinators.parser.{ Term_-> => Term_-> }
import scala.of.coq.parsercombinators.parser.Type
import scala.of.coq.parsercombinators.parser.UncurriedTermApplication
import scala.of.coq.parsercombinators.parser.UnderscorePattern

import org.scalatest.Finders
import org.scalatest.FunSuite
import org.scalatest.Matchers.convertToAnyShouldWrapper

import CustomMatchers.parse
import scala.of.coq.parsercombinators.compiler.ScalaOfCoq
import scala.of.coq.parsercombinators.parser.CoqParser
import java.io.File
import java.net.URL

import TestUtils._
import scala.of.coq.parsercombinators.compiler.Currify

class ScalaOfCoqCurrifiedFileBasedTest extends FunSuite {

  def fileToString(directory: String, extension: String)(fileName: String): String = {
    val fileBufferedSource = io.Source.fromURL(getClass.getResource(directory + "/" + fileName + "." + extension));
    try fileBufferedSource.mkString finally fileBufferedSource.close()
  }

  def actualScalaCode(fileName: String): String = {
    val coqAST = CoqParser(fileToString("", "v")(fileName))

    val optionalCoqAst = Option(coqAST.getOrElse(null))

    val outputString = optionalCoqAst.fold(coqAST.toString) {
      coqTrees =>
        new ScalaOfCoq(coqTrees, Currify).createObjectFileCode(fileName)
    }

    normalizeWhitespace(outputString)
  }

  def expectedScalaCode(fileName: String): String = {
    val fileStringContents = fileToString("/scala/of/coq/generated/code", "scala")(fileName)

    normalizeWhitespace("package .+".r.replaceAllIn(fileStringContents, _ => ""))
  }

  def getListOfFiles(dir: URL): List[String] = {
    val d = new File(dir.getPath)
    if (d.exists && d.isDirectory) {
      d.listFiles.filter(_.isFile).map(_.getName).toList
    } else {
      List[String]()
    }
  }

  ignore("""Testing all Coq file conversions to Scala """) {

    val allCoqFileNames = getListOfFiles(getClass.getResource("/")).filter(_.endsWith(".v"))
    val allBaseNamesWithoutExtension = allCoqFileNames.map(fileName => """(.*/)?([^/]+)\.v$""".r.replaceFirstIn(fileName, "$2"))

    for (name <- allBaseNamesWithoutExtension) {
      println("Testing " + name)
      assert(actualScalaCode(name) === expectedScalaCode(name))
    }

  }

}
