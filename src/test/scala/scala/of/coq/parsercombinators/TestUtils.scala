package scala.of.coq.parsercombinators

import scala.of.coq.parsercombinators.compiler.ScalaOfCoq
import scala.of.coq.parsercombinators.parser.CoqParser

import scala.of.coq.parsercombinators.compiler.CurryingStrategy

import org.scalatest.funsuite.AnyFunSuite

object TestUtils extends AnyFunSuite {
  def normalizeWhitespace(scalaCode: String): String =
    """[\t ]+""".r.replaceAllIn(scalaCode, " ").trim.stripMargin('"')

  def coqParserShouldFailToGenerateScalaCodeFor(coqCode: String)(implicit curryingStrategy: CurryingStrategy): Unit = {
    val parseResult = CoqParser(coqCode)
    assertThrows[IllegalStateException] {
      parseResult.map(new ScalaOfCoq(_, curryingStrategy).generateScalaCode)
    }
  }
}
