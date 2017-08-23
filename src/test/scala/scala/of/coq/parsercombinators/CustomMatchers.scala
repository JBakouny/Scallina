package scala.of.coq.parsercombinators

import org.scalatest._
import matchers._
import scala.of.coq.parsercombinators.parser.CoqAST

import scala.of.coq.parsercombinators.parser.CoqParser
import scala.of.coq.parsercombinators.lexer.CoqLexer

import scala.util.parsing.combinator.token.Tokens
import scala.of.coq.parsercombinators.parser.CoqParser
import scala.util.parsing.combinator.lexical.StdLexical
import scala.of.coq.parsercombinators.compiler.ScalaOfCoq
import scala.of.coq.parsercombinators.parser.Sentence

import TestUtils._

trait CustomMatchers {

  class TokenParserMatcher[T](expected: T) extends Matcher[CoqParser.ParseResult[T]] {

    def apply(left: CoqParser.ParseResult[T]) = {
      val actual = Option(left.getOrElse(null));

      MatchResult(
        actual == Some(expected),
        s"""Expected "$expected" but obtained "$left" """,
        s"""Successfully parsed "$expected" """
      )
    }
  }

  class ScalaCodeMatcher(expected: String, scalaOfCoq: ScalaOfCoq) extends Matcher[CoqParser.ParseResult[List[Sentence]]] {
    def apply(left: CoqParser.ParseResult[List[Sentence]]) = {
      val expectedCode = normalizeWhitespace(expected)
      val actualCode = normalizeWhitespace(left.map(scalaOfCoq.toScalaCode(_)).getOrElse(left.toString));

      MatchResult(
        actualCode == expectedCode,
        s"""Expected "$expectedCode" but obtained "$actualCode" """,
        s"""Successfully parsed "$expectedCode" """
      )
    }
  }

  class LexemMatcher[T](expected: T) extends Matcher[CoqLexer.ParseResult[T]] {

    def apply(left: CoqLexer.ParseResult[T]) = {
      val actual = Option(left.getOrElse(null));

      MatchResult(
        actual == Some(expected),
        s"""Expected "$expected" but obtained "$left" """,
        s"""Successfully parsed "$expected" """
      )
    }
  }

  def parse(coqAst: CoqAST) = new TokenParserMatcher(coqAst)

  def parse(coqAst: List[CoqAST]) = new TokenParserMatcher(coqAst)

  def generateScalaCode(scalaCode: String)(implicit scalaOfCoq: ScalaOfCoq) = new ScalaCodeMatcher(scalaCode, scalaOfCoq)

  def identify(lex: CoqLexer.Token) = new LexemMatcher(lex)
}

// Make them easy to import with:
// import CustomMatchers._
object CustomMatchers extends CustomMatchers
