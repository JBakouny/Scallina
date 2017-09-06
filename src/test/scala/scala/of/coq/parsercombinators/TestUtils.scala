package scala.of.coq.parsercombinators

import scala.of.coq.parsercombinators.compiler.ScalaOfCoq

object TestUtils {
  def normalizeWhitespace(scalaCode: String): String =
    """[\t ]+""".r.replaceAllIn(scalaCode, " ").trim.stripMargin('"')
}
