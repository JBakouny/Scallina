package scala.of.coq.parsercombinators.lexer

import scala.annotation.migration
import scala.util.parsing.combinator.lexical.StdLexical
import scala.util.parsing.input.CharArrayReader
import scala.util.parsing.input.CharArrayReader.EofCh

object CoqLexer extends StdLexical {

  /**
   * Warning: Do not use this method unless you want to parse only one token (even if it is an error token).
   *
   * It is, therefore, preferable to use a Scanner instead of calling this method.
   */
  def apply(s: String) = token(new CharArrayReader(s.toCharArray()))

  /**
   * Warning: Do not use this method unless you plan on continuing if illegal characters are found.
   *
   * It is, therefore, preferable to use a Scanner instead of calling this method.
   */
  def parseAllTokens(s: String) = {
    val scanner = new Scanner(s)

    def parseAllTokensHelper(scanner: CoqLexer.Scanner): List[CoqLexer.Token] = {
      if (scanner.atEnd) Nil
      else (scanner.first) :: parseAllTokensHelper(scanner.rest)
    }

    parseAllTokensHelper(scanner);
  }

  override def whitespace: Parser[Any] = rep[Any](
    whitespaceChar
      | '(' ~ '*' ~ comment
      | '(' ~ '*' ~ failure("unclosed comment")
  )

  override protected def comment: Parser[Any] = (
    rep(chrExcept(EofCh, '*')) ~ '*' ~ ')' ^^ {
      case _ => ' '
    }
    | rep(chrExcept(EofCh, '*')) ~ '*' ~ comment ^^ {
      case _ => ' '
    }
  )

  /*
   * Since strings in Coq cannot be inclosed in single quotes, the corresponding productions were removed from the below overridden token method.
   *
   * Also delimiters were placed in a way so that they take precedence over numbers and identifier:
   * This is needed to parse "_" as a keyword instead of an identifier.
   */
  override def token: Parser[Token] =
    (
      delim // delimiters take precedence
      | identifier
      | number
      | literal
      | EofCh ^^^ EOF
      | '\"' ~> failure("unclosed string literal")
      | failure("illegal character")
    )

  private def identifier: Parser[Token] = {
    identChar ~ ((identChar | digit) *) ^^ { case first ~ rest => processIdent(first :: rest mkString "") }
  }

  /*
   * TODO (Joseph Bakouny): For this first version, only natural numbers will be considered by the lexer.
   * Support for relative integers is scheduled to be incorporated in future versions.
   */
  private def number: Parser[NumericLit] = {
    digit ~ (digit *) ^^ { case first ~ rest => NumericLit(first :: rest mkString "") }
  }

  // TODO (Joseph Bakouny): Add support for integers in future versions.
  /*
  def integer : Parser[INTEGER] = positioned {
    val numberRegexString = "[0-9]+"
    regex((numberRegexString + "| -" + numberRegexString).r) ^^ { (str => INTEGER(str.toInt)) }
  }
  */

  /*
   * TODO (Joseph Bakouny): The definition of a string was simplified for this first version.
   * Consider including the full Coq definition in later versions.
   */
  private def literal: Parser[StringLit] = {
    '\"' ~ (chrExcept('\"', '\n', EofCh) *) ~ '\"' ^^ {
      case '\"' ~ chars ~ '\"' => StringLit(chars mkString "")
      case anythingElse        => throw new IllegalStateException("String literal parser: should not get here!")
    }
  }

  reserved += "as"
  reserved += "at"
  reserved += "cofix"
  reserved += "else"
  reserved += "end"
  reserved += "exists"
  reserved += "exists2"
  reserved += "fix"
  reserved += "for"
  reserved += "forall"
  reserved += "fun"
  reserved += "if"
  reserved += "IF"
  reserved += "in"
  reserved += "let"
  reserved += "match"
  reserved += "mod"
  reserved += "prop"
  reserved += "return"
  reserved += "set"
  reserved += "then"
  reserved += "type"
  reserved += "using"
  reserved += "where"
  reserved += "with"

  // Reserved words added for simplifications (from syntax of terms)
  reserved += "Prop"
  reserved += "Set"
  reserved += "Type"

  delimiters += "()"
  delimiters += "{"
  delimiters += "}"
  delimiters += "("
  delimiters += ")"
  delimiters += ":<"
  delimiters += ":>"
  delimiters += "::"
  delimiters += ":="
  delimiters += ":"
  delimiters += "->"
  delimiters += "=>"
  delimiters += ","
  delimiters += "|-"
  delimiters += "||"
  delimiters += "|"
  delimiters += "_"
  delimiters += "@"
  delimiters += "%"
  delimiters += ".."
  delimiters += ".("
  delimiters += "."
  delimiters += ";"
  delimiters += "=_d"
  delimiters += "=?"
  delimiters += "="
  delimiters += "["
  delimiters += "]"
  delimiters += "!"
  delimiters += "&&"
  delimiters += "&"
  delimiters += "*"
  delimiters += "++"
  delimiters += "+"
  delimiters += "-"
  delimiters += """/\"""
  delimiters += "/"
  delimiters += "<->"
  delimiters += "<-"
  delimiters += "<:"
  delimiters += "<=?"
  delimiters += "<="
  delimiters += "<>"
  delimiters += "<?"
  delimiters += "<"
  delimiters += ">="
  delimiters += ">->"
  delimiters += ">"
  delimiters += "?="
  delimiters += "?"
  delimiters += """\/"""
  delimiters += "^"
  delimiters += "~"

  // Added delimiters:
  delimiters += "'" // for the letPatternIn production

  // TODO (Joseph Bakouny): Investigate further the issue of Vernacular keywords
  // Added Vernacular keywords:
  reserved += "Definition"
  reserved += "Inductive"
  reserved += "Fixpoint"
  reserved += "struct"

  reserved += "Theorem"
  reserved += "Lemma"
  reserved += "Remark"
  reserved += "Fact"
  reserved += "Corollary"
  reserved += "Proposition"
  reserved += "Example"

  reserved += "Proof"
  reserved += "Qed"
  reserved += "Defined"
  reserved += "Admitted"

  reserved += "Require"
  reserved += "Import"
  reserved += "Arguments"
  reserved += "Local"
  reserved += "Open"
  reserved += "Scope"

}
