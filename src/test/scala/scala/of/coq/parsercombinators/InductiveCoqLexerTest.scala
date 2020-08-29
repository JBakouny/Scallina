package scala.of.coq.parsercombinators

import org.scalatest.FunSuite
import org.scalatest.Matchers.{contain, convertToAnyShouldWrapper}

import scala.of.coq.parsercombinators.lexer.CoqLexer
import scala.of.coq.parsercombinators.lexer.CoqLexer.{Identifier, Keyword, errorToken}

class InductiveCoqLexerTest extends FunSuite {

  val validCoqCode =
    """
    Inductive ExceptionM (A : Type) :=
      Return (a : A)
    | Raise (e: Exception).
    """

  val expectedLexerOutput = List(
    Keyword("Inductive"),
    Identifier("ExceptionM"),
    Keyword("("),
    Identifier("A"),
    Keyword(":"),
    Keyword("Type"),
    Keyword(")"),
    Keyword(":="),
    Identifier("Return"),
    Keyword("("),
    Identifier("a"),
    Keyword(":"),
    Identifier("A"),
    Keyword(")"),
    Keyword("|"),
    Identifier("Raise"),
    Keyword("("),
    Identifier("e"),
    Keyword(":"),
    Identifier("Exception"),
    Keyword(")"),
    Keyword(".")
  )

  val invalidCoqCode: String =
    """
  "Inductive ExceptionM (A : Type) `
  "  Return (a : A)
  "| Raise (e: Exception).
  """.stripMargin('"')

  test("Coq Lexer succeeds in parsing valid Coq code") {
    CoqLexer.parseAllTokens(validCoqCode) shouldEqual expectedLexerOutput
  }

  test("Coq Lexer fails if Coq code contains an invalid symbol") {
    CoqLexer.parseAllTokens(invalidCoqCode) should contain(errorToken("illegal character"))
  }

}
