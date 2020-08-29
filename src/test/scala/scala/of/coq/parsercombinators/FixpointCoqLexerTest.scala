package scala.of.coq.parsercombinators

import org.scalatest.FunSuite
import org.scalatest.Matchers.{contain, convertToAnyShouldWrapper}

import scala.of.coq.parsercombinators.lexer.CoqLexer
import scala.of.coq.parsercombinators.lexer.CoqLexer.{Identifier, Keyword, NumericLit, errorToken}

class FixpointCoqLexerTest extends FunSuite {

  val validCoqCode =
    """
    Fixpoint sum_n n := match n with
      0 => 0
    | S p =>  plus p (sum_n p)
    end.
    """

  val expectedLexerOutput = List(
    Keyword("Fixpoint"),
    Identifier("sum_n"),
    Identifier("n"),
    Keyword(":="),
    Keyword("match"),
    Identifier("n"),
    Keyword("with"),
    NumericLit("0"),
    Keyword("=>"),
    NumericLit("0"),
    Keyword("|"),
    Identifier("S"),
    Identifier("p"),
    Keyword("=>"),
    Identifier("plus"),
    Identifier("p"),
    Keyword("("),
    Identifier("sum_n"),
    Identifier("p"),
    Keyword(")"),
    Keyword("end"),
    Keyword(".")
  )

  val invalidCoqCode: String =
    """
  "Fixpoint sum_n n ` match n with
  "  0 => 0
  "| S p =>  plus p (sum_n p)
  "end.
  """.stripMargin('"')

  test("Coq Lexer succeeds in parsing valid Coq code") {
    CoqLexer.parseAllTokens(validCoqCode) shouldEqual expectedLexerOutput
  }

  test("Coq Lexer fails if Coq code contains an invalid symbol") {
    CoqLexer.parseAllTokens(invalidCoqCode) should contain(errorToken("illegal character"))
  }

}
