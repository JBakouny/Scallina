package scala.of.coq.parsercombinators

import org.scalatest.Finders
import org.scalatest.FunSuite
import org.scalatest.Matchers.contain
import org.scalatest.Matchers.convertToAnyShouldWrapper

import scala.of.coq.parsercombinators.lexer.CoqLexer.Identifier
import scala.of.coq.parsercombinators.lexer.CoqLexer.Keyword
import scala.of.coq.parsercombinators.lexer.CoqLexer.NumericLit
import scala.of.coq.parsercombinators.lexer.CoqLexer.errorToken
import lexer.CoqLexer

class DefinitionCoqLexerTest extends FunSuite {

  val validCoqCode =
    """
    Definition f x := plus x 1.
    """

  val expectedLexerOutput = List(
    Keyword("Definition"), Identifier("f"), Identifier("x"), Keyword(":="),
    Identifier("plus"), Identifier("x"), NumericLit("1"), Keyword(".")
  )

  val invalidCoqCode =
    """
  "Definition f x ` plus x 1.
  """.stripMargin('"');

  test("Coq Lexer succeeds in parsing valid Coq code") {
    CoqLexer.parseAllTokens(validCoqCode) shouldEqual expectedLexerOutput
  }

  test("Coq Lexer fails if Coq code contains an invalid symbol") {
    CoqLexer.parseAllTokens(invalidCoqCode) should contain (errorToken("illegal character"))
  }

}
