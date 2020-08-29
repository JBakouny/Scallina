package scala.of.coq.parsercombinators

import org.scalatest.matchers._

import scala.of.coq.parsercombinators.TestUtils._
import scala.of.coq.parsercombinators.compiler.{CurryingStrategy, ScalaOfCoq}
import scala.of.coq.parsercombinators.lexer.CoqLexer
import scala.of.coq.parsercombinators.parser.{CoqAST, CoqParser, Sentence}

trait CustomMatchers {

  class TokenParserMatcher[T](expected: T) extends Matcher[CoqParser.ParseResult[T]] {

    def apply(left: CoqParser.ParseResult[T]): MatchResult = {
      val actual = Option(left.getOrElse(null))

      MatchResult(
        actual.contains(expected),
        s"""Expected "$expected" but obtained "$left" """,
        s"""Successfully parsed "$expected" """
      )
    }
  }

  class ScalaCodeMatcher(expected: String, curryingStrategy: CurryingStrategy)
      extends Matcher[CoqParser.ParseResult[List[Sentence]]] {
    def apply(left: CoqParser.ParseResult[List[Sentence]]): MatchResult = {

      val expectedCode = normalizeWhitespace(expected)
      val actualCode = normalizeWhitespace(
        left
          .map(new ScalaOfCoq(_, curryingStrategy).generateScalaCode)
          .getOrElse(left.toString)
      )

      MatchResult(
        actualCode == expectedCode,
        s"""Expected "$expectedCode" but obtained "$actualCode" """,
        s"""Successfully parsed "$expectedCode" """
      )
    }
  }

  class LexemMatcher[T](expected: T) extends Matcher[CoqLexer.ParseResult[T]] {

    def apply(left: CoqLexer.ParseResult[T]): MatchResult = {
      val actual = Option(left.getOrElse(null))

      MatchResult(
        actual.contains(expected),
        s"""Expected "$expected" but obtained "$left" """,
        s"""Successfully parsed "$expected" """
      )
    }
  }

  def parse(coqAst: CoqAST): TokenParserMatcher[CoqAST] = new TokenParserMatcher(coqAst)

  def parse(coqAst: List[CoqAST]): TokenParserMatcher[List[CoqAST]] = new TokenParserMatcher(coqAst)

  def generateScalaCode(scalaCode: String)(implicit curryingStrategy: CurryingStrategy): ScalaCodeMatcher =
    new ScalaCodeMatcher(scalaCode, curryingStrategy)

  def identify(lex: CoqLexer.Token): LexemMatcher[CoqLexer.Token] = new LexemMatcher(lex)
}

// Make them easy to import with:
// import CustomMatchers._
object CustomMatchers extends CustomMatchers
