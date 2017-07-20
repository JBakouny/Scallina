package scala.of.coq.parsercombinators.parser

import scala.of.coq.parsercombinators.parser.CoqParser._

object CoqTermParser {
  def apply(code: String): ParseResult[CoqAST] = CoqParser.parseTerm(code)
}
