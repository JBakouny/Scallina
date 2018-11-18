package scala.of.coq.parsercombinators

import scala.of.coq.parsercombinators.compiler.ScalaOfCoq
import scala.of.coq.parsercombinators.parser.CoqParser
import scala.of.coq.parsercombinators.compiler.CurryingStrategy
import org.scalatest.{Assertion, FunSuite}

object TestUtils extends FunSuite {
  def normalizeWhitespace(scalaCode: String): String =
    """[\t ]+""".r.replaceAllIn(scalaCode, " ").trim.stripMargin('"')

  def coqParserShouldFailToGenerateScalaCodeFor(coqCode: String)(
      implicit curryingStrategy: CurryingStrategy): Assertion = {
    val parseResult = CoqParser(coqCode)
    assertThrows[IllegalStateException] {
      parseResult.map(new ScalaOfCoq(_, curryingStrategy).generateScalaCode)
    }
  }
}
