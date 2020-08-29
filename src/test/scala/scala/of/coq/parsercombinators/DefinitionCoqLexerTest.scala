package scala.of.coq.parsercombinators

import org.scalatest.FunSuite
import org.scalatest.Matchers.{contain, convertToAnyShouldWrapper}

import scala.of.coq.parsercombinators.lexer.CoqLexer
import scala.of.coq.parsercombinators.lexer.CoqLexer.{Identifier, Keyword, NumericLit, errorToken}

class DefinitionCoqLexerTest extends FunSuite {

  val validCoqCode =
    """
    Definition f x := plus x 1.
    """

  val expectedLexerOutput = List(
    Keyword("Definition"),
    Identifier("f"),
    Identifier("x"),
    Keyword(":="),
    Identifier("plus"),
    Identifier("x"),
    NumericLit("1"),
    Keyword(".")
  )

  val invalidCoqCode: String =
    """
  "Definition f x ` plus x 1.
  """.stripMargin('"')

  test("Coq Lexer succeeds in parsing valid Coq code") {
    CoqLexer.parseAllTokens(validCoqCode) shouldEqual expectedLexerOutput
  }

  test("Coq Lexer fails if Coq code contains an invalid symbol") {
    CoqLexer.parseAllTokens(invalidCoqCode) should contain(errorToken("illegal character"))
  }

}
