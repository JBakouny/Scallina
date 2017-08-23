package scala.of.coq.parsercombinators

import scala.of.coq.parsercombinators.compiler.Currify
import scala.of.coq.parsercombinators.compiler.ScalaOfCoq
import scala.of.coq.parsercombinators.compiler.NoCurrying

object TestUtils {
  def normalizeWhitespace(scalaCode: String): String =
    """[\t ]+""".r.replaceAllIn(scalaCode, " ").trim.stripMargin('"')

  val currifiedScalaOfCoq = new ScalaOfCoq(Currify)
  val uncurrifiedScalaOfCoq = new ScalaOfCoq(NoCurrying)
}
