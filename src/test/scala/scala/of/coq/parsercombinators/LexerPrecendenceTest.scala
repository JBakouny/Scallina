package scala.of.coq.parsercombinators

import org.scalatest.Finders
import org.scalatest.FunSuite
import org.scalatest.Matchers.convertToAnyShouldWrapper

import CustomMatchers.identify
import scala.of.coq.parsercombinators.lexer.CoqLexer.Identifier
import scala.of.coq.parsercombinators.lexer.CoqLexer.Keyword
import scala.of.coq.parsercombinators.lexer.CoqLexer.NumericLit
import scala.of.coq.parsercombinators.lexer.CoqLexer.StringLit
import lexer.CoqLexer
/**
 * While implementing the lexer, care should be
 * taken to, for example, identify the "::" token before the ":" token.
 *
 * The role of these tests is to make sure that all tokens are identified correctly by the lexer.
 *
 * There should be a test for each lexer token.
 *
 */
class LexerPrecendenceTest extends FunSuite {

  test("""lexer identifies "myVar" Identifier""") { CoqLexer("myVar") should identify (Identifier("myVar")) }
  test("""lexer identifies "my_2nd_var" Identifier""") { CoqLexer("my_2nd_var") should identify (Identifier("my_2nd_var")) }

  test("""lexer identifies "my_1st_string" STRING""") { CoqLexer(""""my_1st_string"""") should identify (StringLit("my_1st_string")) }

  test("""lexer identifies "37" NUMBER""") { CoqLexer("37") should identify (NumericLit("37")) }

  test("lexer identifies as") { CoqLexer("as") should identify (Keyword("as")) }
  test("lexer identifies at") { CoqLexer("at") should identify (Keyword("at")) }
  test("lexer identifies cofix") { CoqLexer("cofix") should identify (Keyword("cofix")) }
  test("lexer identifies else") { CoqLexer("else") should identify (Keyword("else")) }
  test("lexer identifies end") { CoqLexer("end") should identify (Keyword("end")) }
  test("lexer identifies exists") { CoqLexer("exists") should identify (Keyword("exists")) }
  test("lexer identifies exists2") { CoqLexer("exists2") should identify (Keyword("exists2")) }
  test("lexer identifies fix") { CoqLexer("fix") should identify (Keyword("fix")) }
  test("lexer identifies for") { CoqLexer("for") should identify (Keyword("for")) }
  test("lexer identifies forall") { CoqLexer("forall") should identify (Keyword("forall")) }
  test("lexer identifies fun") { CoqLexer("fun") should identify (Keyword("fun")) }
  test("lexer identifies if") { CoqLexer("if") should identify (Keyword("if")) }
  test("lexer identifies IF") { CoqLexer("IF") should identify (Keyword("IF")) }
  test("lexer identifies in") { CoqLexer("in") should identify (Keyword("in")) }
  test("lexer identifies let") { CoqLexer("let") should identify (Keyword("let")) }
  test("lexer identifies match") { CoqLexer("match") should identify (Keyword("match")) }
  test("lexer identifies mod") { CoqLexer("mod") should identify (Keyword("mod")) }
  test("lexer identifies prop") { CoqLexer("prop") should identify (Keyword("prop")) }
  test("lexer identifies return") { CoqLexer("return") should identify (Keyword("return")) }
  test("lexer identifies set") { CoqLexer("set") should identify (Keyword("set")) }
  test("lexer identifies then") { CoqLexer("then") should identify (Keyword("then")) }
  test("lexer identifies type") { CoqLexer("type") should identify (Keyword("type")) }
  test("lexer identifies using") { CoqLexer("using") should identify (Keyword("using")) }
  test("lexer identifies where") { CoqLexer("where") should identify (Keyword("where")) }
  test("lexer identifies with") { CoqLexer("with") should identify (Keyword("with")) }
  test("lexer identifies ()") { CoqLexer("()") should identify (Keyword("()")) }
  test("lexer identifies {") { CoqLexer("{") should identify (Keyword("{")) }
  test("lexer identifies }") { CoqLexer("}") should identify (Keyword("}")) }
  test("lexer identifies (") { CoqLexer("(") should identify (Keyword("(")) }
  test("lexer identifies )") { CoqLexer(")") should identify (Keyword(")")) }
  test("lexer identifies :<") { CoqLexer(":<") should identify (Keyword(":<")) }
  test("lexer identifies :>") { CoqLexer(":>") should identify (Keyword(":>")) }
  test("lexer identifies ::") { CoqLexer("::") should identify (Keyword("::")) }
  test("lexer identifies :=") { CoqLexer(":=") should identify (Keyword(":=")) }
  test("lexer identifies :") { CoqLexer(":") should identify (Keyword(":")) }
  test("lexer identifies ->") { CoqLexer("->") should identify (Keyword("->")) }
  test("lexer identifies =>") { CoqLexer("=>") should identify (Keyword("=>")) }
  test("lexer identifies ,") { CoqLexer(",") should identify (Keyword(",")) }
  test("lexer identifies |") { CoqLexer("|") should identify (Keyword("|")) }
  test("lexer identifies _") { CoqLexer("_") should identify (Keyword("_")) }
  test("lexer identifies @") { CoqLexer("@") should identify (Keyword("@")) }
  test("lexer identifies %") { CoqLexer("%") should identify (Keyword("%")) }
  test("lexer identifies ..") { CoqLexer("..") should identify (Keyword("..")) }
  test("lexer identifies .(") { CoqLexer(".(") should identify (Keyword(".(")) }
  test("lexer identifies .") { CoqLexer(".") should identify (Keyword(".")) }
  test("lexer identifies ;") { CoqLexer(";") should identify (Keyword(";")) }
  test("lexer identifies =_d") { CoqLexer("=_d") should identify (Keyword("=_d")) }
  test("lexer identifies =") { CoqLexer("=") should identify (Keyword("=")) }
  test("lexer identifies [") { CoqLexer("[") should identify (Keyword("[")) }
  test("lexer identifies ]") { CoqLexer("]") should identify (Keyword("]")) }
  test("lexer identifies !") { CoqLexer("!") should identify (Keyword("!")) }
  test("lexer identifies &&") { CoqLexer("&&") should identify (Keyword("&&")) }
  test("lexer identifies &") { CoqLexer("&") should identify (Keyword("&")) }
  test("lexer identifies *") { CoqLexer("*") should identify (Keyword("*")) }
  test("lexer identifies ++") { CoqLexer("++") should identify (Keyword("++")) }
  test("lexer identifies +") { CoqLexer("+") should identify (Keyword("+")) }
  test("lexer identifies -") { CoqLexer("-") should identify (Keyword("-")) }
  test("""lexer identifies /\""") { CoqLexer("""/\""") should identify (Keyword("""/\""")) }
  test("lexer identifies /") { CoqLexer("/") should identify (Keyword("/")) }
  test("lexer identifies <->") { CoqLexer("<->") should identify (Keyword("<->")) }
  test("lexer identifies <-") { CoqLexer("<-") should identify (Keyword("<-")) }
  test("lexer identifies <:") { CoqLexer("<:") should identify (Keyword("<:")) }
  test("lexer identifies <=") { CoqLexer("<=") should identify (Keyword("<=")) }
  test("lexer identifies <>") { CoqLexer("<>") should identify (Keyword("<>")) }
  test("lexer identifies <") { CoqLexer("<") should identify (Keyword("<")) }
  test("lexer identifies >=") { CoqLexer(">=") should identify (Keyword(">=")) }
  test("lexer identifies >->") { CoqLexer(">->") should identify (Keyword(">->")) }
  test("lexer identifies >") { CoqLexer(">") should identify (Keyword(">")) }
  test("lexer identifies ?=") { CoqLexer("?=") should identify (Keyword("?=")) }
  test("lexer identifies ?") { CoqLexer("?") should identify (Keyword("?")) }
  test("""lexer identifies \/""") { CoqLexer("""\/""") should identify (Keyword("""\/""")) }
  test("lexer identifies ^") { CoqLexer("^") should identify (Keyword("^")) }
  test("lexer identifies |-") { CoqLexer("|-") should identify (Keyword("|-")) }
  test("lexer identifies ||") { CoqLexer("||") should identify (Keyword("||")) }
  test("lexer identifies ~") { CoqLexer("~") should identify (Keyword("~")) }

}
