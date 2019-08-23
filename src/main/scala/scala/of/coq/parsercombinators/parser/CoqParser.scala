package scala.of.coq.parsercombinators.parser

import scala.annotation.migration
import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.syntactical.StandardTokenParsers

import scala.of.coq.parsercombinators.lexer.CoqLexer
import scala.of.coq.parsercombinators.lexer.CoqLexer.Identifier
import scala.of.coq.parsercombinators.lexer.CoqLexer.NumericLit
import scala.of.coq.parsercombinators.lexer.CoqLexer.StringLit

object CoqParser extends StandardTokenParsers with PackratParsers {

  override val lexical = CoqLexer

  def apply(s: String): ParseResult[List[Sentence]] = {
    val reader = new lexical.Scanner(s)
    program(reader)
  }

  def parseTerm(s: String): ParseResult[CoqAST] = {
    val reader = new lexical.Scanner(s)
    phrase(Term.term)(reader)
  }

  private lazy val program = {
    phrase(sentence +)
  }

  type P[+T] = PackratParser[T]

  lazy val sentence: P[Sentence] = (
    importCommand
    | loadCommand
    | argumentsCommand
    | setCommand
    | scopeCommand
    | definition
    | inductive
    | record
    | fixPoint
    | functionDef
    | assertion <~ proof)

  //TODO (Joseph Bakouny): This production is not in the official grammar... consider a more in-depth support for modules.
  private lazy val importCommand: P[RequireImport] = (
    opt("From" ~ qualid) ~ "Require" ~ "Import" ~> qualid <~ "." ^^ { RequireImport(_, false) }
    | opt("Require") ~ "Export" ~> qualid <~ "." ^^ { RequireImport(_, true) })

  private lazy val loadCommand: P[LoadCommand] =
    "Load" ~> qualid <~ "." ^^ { LoadCommand(_) }

  /*
   *  NOTE: This production is not in the grammar, it supports the commands of the form:
   *  Arguments Leaf {A} _.
   *  Arguments Node {A} _ _.
   */
  private lazy val argumentsCommand: P[ArgumentsCommand] =
    "Arguments" ~> qualid ~ binders <~ "." ^^ {
      case id ~ binders => ArgumentsCommand(id, binders)
    }

  private lazy val setCommand: P[SetCommand] = {
    "Set" ~> rep(ident) <~ "." ^^ { xs => SetCommand(xs mkString " ") }
  }

  /*
   *  NOTE: This production is not in the grammar, it supports the commands of the form:
   *  Local Open Scope Z_scope.
   *  or
   *  Open Scope Z_scope.
   */
  private lazy val scopeCommand: P[ScopeCommand] =
    ("Local"?) ~ "Open" ~ "Scope" ~ qualid <~ "." ^^ {
      case localOptional ~ open ~ scope ~ scopeName => ScopeCommand(scopeName, localOptional.isDefined)
    }

  /*
   * TODO (Joseph Bakouny): Add [Local] keyword and "Let" production to Definition in subsequent versions
   */
  private lazy val definition: P[Definition] =
    "Definition" ~> identifier ~ (binders ?) ~ opt(":" ~> term) ~ ":=" ~ term <~ "." ^^ {
      case id ~ binders ~ typeTerm ~ lex_:= ~ bodyTerm => Definition(id, binders, typeTerm, bodyTerm)
    }

  // TODO (Joseph Bakouny): Consider supporting a list of inductive bodies and CoInductives
  private lazy val inductive: P[Inductive] =
    "Inductive" ~> inductiveBody <~ "." ^^ { Inductive(_) }

  // TODO (Joseph Bakouny): Check why the InductiveBody typeTerm seems optional in Coq but marked as required in the grammar
  private lazy val inductiveBody: P[InductiveBody] =
    identifier ~ (binders ?) ~ opt(":" ~> term) ~ ":=" ~ opt(("|" ?) ~> rep1sep(inductiveBodyItem, "|")) ^^ {
      case id ~ binders ~ typeTerm ~ lex_:= ~ inductiveBodyItems =>
        InductiveBody(id, binders, typeTerm, inductiveBodyItems.fold(List[InductiveBodyItem]())(xs => xs))
    }

  /**
   * This is just a helper function used in the function inductiveBody, it is not present in the original grammar.
   */
  private lazy val inductiveBodyItem: P[InductiveBodyItem] =
    identifier ~ (binders ?) ~ opt(":" ~> term) ^^ {
      case id ~ binders ~ typeTerm => InductiveBodyItem(id, binders, typeTerm)
    }

  private lazy val record: P[Record] =
    recordKeyword ~ identifier ~ (binders ?) ~ opt(":" ~> sort) ~ ":=" ~ (identifier ?) ~ ("{" ~> repsep(recordField, ";")) <~ "}" ~ "." ^^ {
      case keyword ~ id ~ binders ~ sort ~ lex_:= ~ constructor ~ fields => Record(keyword, id, binders, sort, constructor, fields)
    }

  private lazy val recordKeyword: P[RecordKeyword] =
    accept("recordKeyword", {
      case CoqLexer.Keyword("Record")      => RecordKeyword
      case CoqLexer.Keyword("Structure")   => StructureKeyword
      // TODO(Joseph Bakouny): These two record keywords are currently not supported.
      case CoqLexer.Keyword("Inductive")   => InductiveRecordKeyword
      case CoqLexer.Keyword("CoInductive") => CoInductiveRecordKeyword
    })

  private lazy val concreteRecordField: P[ConcreteRecordField] =
    name ~ (binders ?) ~ opt(":" ~> term) ~ ":=" ~ term ^^ {
      case name ~ binders ~ typeTerm ~ lex_:= ~ bodyTerm => ConcreteRecordField(name, binders, typeTerm, bodyTerm)
    }

  private lazy val abstractRecordField: P[AbstractRecordField] =
    name ~ (binders ?) ~ ":" ~ term ^^ {
      case name ~ binders ~ lex_: ~ typeTerm => AbstractRecordField(name, binders, typeTerm)
    }

  private lazy val recordField: P[RecordField] = (
    concreteRecordField
    | abstractRecordField)

  // TODO (Joseph Bakouny): Consider supporting list of fixBodies for a Fixpoint and also CoFixpoint
  private lazy val fixPoint: P[Fixpoint] =
    "Fixpoint" ~> fixBody <~ "." ^^ { Fixpoint(_) }

  private lazy val functionDef: P[FunctionDef] =
    "Function" ~> functionBody <~ "." ~ (proof ?) ^^ { FunctionDef(_) }

  private lazy val assertion: P[Assertion] =
    assertionKeyword ~ identifier ~ (binders ?) ~ ":" ~ term <~ "." ^^ {
      case keyword ~ id ~ binders ~ lex_: ~ term => Assertion(keyword, id, binders, term)
    }

  private lazy val assertionKeyword: P[AssertionKeyword] =
    accept("assertionKeyword", {
      case CoqLexer.Keyword("Theorem")     => Theorem
      case CoqLexer.Keyword("Lemma")       => Lemma
      case CoqLexer.Keyword("Remark")      => Remark
      case CoqLexer.Keyword("Fact")        => Fact
      case CoqLexer.Keyword("Corollary")   => Corollary
      case CoqLexer.Keyword("Proposition") => Proposition
      case CoqLexer.Keyword("Definition")  => DefinitionAssertionKeyword
      case CoqLexer.Keyword("Example")     => Example
    })

  /*
   * TODO (Joseph Bakouny): Check how to parse and store proofs correctly if needed
   * (note: the grammar is not specified in the Coq Manual Vernacular productions).
   */
  private lazy val proof: P[Proof] = {
    val failureMsg = "A Coq proof is expected"
    lazy val proofEnd: P[Proof] = (
      rep(acceptIf(_ != CoqLexer.Keyword("Qed"))(_ => failureMsg)) ~ "Qed" ^^ { _ => ProofQed }
      | rep(acceptIf(_ != CoqLexer.Keyword("Defined"))(_ => failureMsg)) ~ "Defined" ^^ { _ => ProofDefined }
      | rep(acceptIf(_ != CoqLexer.Keyword("Admitted"))(_ => failureMsg)) ~ "Admitted" ^^ { _ => ProofAdmitted })

    "Proof" ~ "." ~> proofEnd <~ "."
  }

  private lazy val term: P[Term] = Term.term

  private lazy val binders: P[Binders] = {
    (binder +) ^^ { case bs => Binders(bs) }
  }

  private lazy val binder: P[Binder] = (
    name ^^ { ExplicitSimpleBinder(_) }
    | "(" ~> (name +) ~ ":" ~ term <~ ")" ^^ {
      case names ~ lex_: ~ typeTerm => ExplicitBinderWithType(names, typeTerm)
    }
    | "{" ~> (name +) ~ opt(":" ~> term) <~ "}" ^^ {
      case names ~ typeTerm => ImplicitBinder(names, typeTerm)
    })

  private lazy val name: P[Name] = {
    accept("name", {
      case id @ Identifier(name) => Name(Some(Ident(name)))
      case CoqLexer.Keyword("_") => Name(None)
    })
  }

  private lazy val qualid: P[Qualid] =
    rep1sep(identifier, ".") ^^ { Qualid(_) }

  private lazy val sort: P[Sort] =
    accept("sort", {
      case CoqLexer.Keyword("Prop") => Prop
      case CoqLexer.Keyword("Set")  => Set
      case CoqLexer.Keyword("Type") => Type
    })

  // TODO (Joseph Bakouny): consider adding the original definition of fixBody outside AbstractTerm
  private lazy val fixBody: P[FixBody] = Term.fixBody
  private lazy val functionBody: P[FunctionBody] = Term.functionBody

  /**
   * This is just a helper function used in the function matchItem, it is not present in the original grammar.
   */
  private lazy val matchItemPattern: P[MatchItemPattern] =
    qualid ~ (pattern *) ^^ { case id ~ patterns => MatchItemPattern(id, patterns) }

  private lazy val multPattern: P[MultPattern] =
    rep1sep(pattern, ",") ^^ { MultPattern(_) }

  private lazy val pattern: P[Pattern] = Pattern.pattern

  private lazy val orPattern: P[OrPattern] =
    rep1sep(pattern, "|") ^^ { OrPattern(_) }

  private lazy val identifier: P[Ident] = {
    accept("identifier", { case Identifier(name) => Ident(name) })
  }

  private lazy val numberLiteral: P[Number] = {
    accept("number literal", { case NumericLit(n) => Number(n.toInt) })
  }

  // TODO (Joseph Bakouny): The stringLiteral production is not used yet. It should either be used or removed.
  private lazy val stringLiteral: P[StringLit] = {
    accept("string literal", { case lit @ StringLit(name) => lit })
  }

  private lazy val parenthesis: P[BetweenParenthesis] =
    "(" ~> Term.term <~ ")" ^^ { BetweenParenthesis(_) }

  /*
   * NOTE: This production is not in the grammar, it supports Coq tuple values of the form:
   * (k,v)
   */
  private lazy val tupleValue: P[TupleValue] =
    "(" ~> repsep(Term.term, ",") <~ ")" ^^ { TupleValue(_) }

  private abstract class AbstractTerm {

    lazy val term: P[Term] = (
      forall
      | fun
      | fix
      | simpleLetIn
      | letFixIn
      | letConstructorArgsIn
      | letPatternIn
      | termIf
      | term_:
      | term_<:
      | term_:>
      | term_->
      | explicitQualidApplication
      | termApplication
      | term_%
      | infixOperator
      | patternMatch
      | recordProjection
      | qualid
      | sort
      | numberLiteral
      | parenthesis
      | tupleValue
      | recordInstantiation)

    /**
     * This method is abstract and therefore allows every subclass of AbstractTermProductions to define a custom termApplication.
     */
    protected def termApplication: P[UncurriedTermApplication]

    private lazy val forall: P[ForAll] =
      "forall" ~> binders ~ "," ~ term ^^ { case bs ~ comma ~ t => ForAll(bs, t) }

    private lazy val fun: P[Fun] =
      "fun" ~> binders ~ "=>" ~ term ^^ {
        case bs ~ lex_=> ~ t => Fun(bs, t)
      }

    private lazy val fix: P[Fix] =
      "fix" ~> fixBodies ^^ { Fix(_) }

    private lazy val simpleLetIn: P[SimpleLetIn] =
      "let" ~> identifier ~ (binders ?) ~ (":" ~> term ?) ~ ":=" ~ term ~ "in" ~ term ^^ {
        case id ~ binders ~ typeTerm ~ lex_:= ~ inputTerm ~ in ~ mainTerm => SimpleLetIn(id, binders, typeTerm, inputTerm, mainTerm)
      }

    private lazy val letFixIn: P[LetFixIn] =
      "let" ~ "fix" ~> fixBody ~ "in" ~ term ^^ {
        case fixBody ~ in ~ mainTerm => LetFixIn(fixBody, mainTerm)
      }

    private lazy val letConstructorArgsIn: P[LetConstructorArgsIn] =
      "let" ~> ("(" ~> repsep(name, ",") <~ ")") ~ (depRetType ?) ~ ":=" ~ term ~ "in" ~ term ^^ {
        case names ~ depRetType ~ lex_:= ~ inputTerm ~ in ~ mainTerm =>
          LetConstructorArgsIn(names, depRetType, inputTerm, mainTerm)
      }

    private lazy val letPatternIn: P[LetPatternIn] =
      "let" ~ "'" ~> pattern ~ ":=" ~ term ~ (returnType ?) ~ "in" ~ term ^^ {
        case pattern ~ lex_:= ~ inputTerm ~ returnType ~ in ~ mainTerm => LetPatternIn(pattern, inputTerm, returnType, mainTerm)
      }

    private lazy val termIf: P[TermIf] =
      "if" ~> term ~ (depRetType ?) ~ "then" ~ term ~ "else" ~ term ^^ {
        case cond ~ depRetType ~ thenKeyword ~ thenPart ~ elseKeyword ~ elsePart => TermIf(cond, depRetType, thenPart, elsePart)
      }

    private lazy val term_: : P[Term_:] =
      term ~ ":" ~ term ^^ { case termA ~ lex_: ~ termB => Term_:(termA, termB) }

    private lazy val term_<: : P[Term_<:] =
      term ~ "<:" ~ term ^^ { case termA ~ lex_<: ~ termB => Term_<:(termA, termB) }

    private lazy val term_:> : P[Term_:>] =
      term <~ ":>" ^^ { Term_:>(_) }

    private lazy val term_-> : P[Term_->] =
      term ~ "->" ~ term ^^ { case termA ~ lex_-> ~ termB => Term_->(termA, termB) }

    // TODO (Joseph Bakouny): Review the use of "TermWithoutApplication.term" instead of "term" in the below "explicitQualidApplication" production
    private lazy val explicitQualidApplication: P[ExplicitQualidApplication] =
      "@" ~> qualid ~ (TermWithoutApplication.term *) ^^ { case id ~ arguments => ExplicitQualidApplication(id, arguments) }

    private lazy val term_% : P[Term_%] =
      term ~ "%" ~ identifier ^^ { case term ~ lex_% ~ identifier => Term_%(term, identifier) }

    //TODO (Joseph Bakouny): Consider a more elegant representation of infix operators
    /*
     * Warning: infix operators are not represented in the Coq grammar, this class should be rethinked!
     */
    private lazy val infixOperator: P[InfixOperator] = {
      def infixOp(op: String) =
        term ~ op ~ term ^^ { case leftOp ~ op ~ rightOp => InfixOperator(leftOp, op, rightOp) }

      (
        infixOp("+")
        | infixOp("-")
        | infixOp("*")
        | infixOp("/")
        | infixOp(">")
        | infixOp("<")
        | infixOp("=")
        | infixOp("<=?")
        | infixOp("<=")
        | infixOp(">=")
        | infixOp("<?")
        | infixOp("=?")
        | infixOp("::"))
    }

    private lazy val patternMatch: P[Match] =
      "match" ~> rep1sep(matchItem, ",") ~ (returnType ?) ~ "with" ~ opt(("|" ?) ~> rep1sep(patternEquation, "|")) <~ "end" ^^ {
        case matchItems ~ returnType ~ withKeyword ~ equations => Match(matchItems, returnType, equations.fold(List[PatternEquation]())(xs => xs))
      }

    /*
     * TODO (Joseph Bakouny): For the moment, we consider that a fixBodies only contains one fixBody.
     * In subsequent versions, fixBodies should contain a list of fixBody.
     */
    private lazy val fixBodies: P[FixBodies] =
      fixBody ^^ { FixBodies(_) }

    lazy val fixBody: P[FixBody] =
      identifier ~ binders ~ (fixAnnotation ?) ~ opt(":" ~> term) ~ ":=" ~ term ^^ {
        case id ~ binders ~ annotation ~ typeTerm ~ lex_:= ~ bodyTerm => FixBody(id, binders, annotation, typeTerm, bodyTerm)
      }

    lazy val functionBody: P[FunctionBody] =
      identifier ~ binders ~ annotation ~ opt(":" ~> term) ~ ":=" ~ term ^^ {
        case id ~ binders ~ annotation ~ typeTerm ~ lex_:= ~ bodyTerm => FunctionBody(id, binders, annotation, typeTerm, bodyTerm)
      }

    private lazy val matchItem: P[MatchItem] =
      term ~ opt("as" ~> name) ~ opt("in" ~> matchItemPattern) ^^ {
        case term ~ name ~ matchItemPattern => MatchItem(term, name, matchItemPattern)
      }

    private lazy val depRetType: P[DepRetType] =
      ("as" ~> name ?) ~ returnType ^^ { case optName ~ returnType => DepRetType(optName, returnType) }

    private lazy val returnType: P[ReturnType] =
      "return" ~> term ^^ { ReturnType(_) }

    private lazy val patternEquation: P[PatternEquation] =
      rep1sep(multPattern, "|") ~ "=>" ~ term ^^ { case orMultPatterns ~ lex_=> ~ outputTerm => PatternEquation(orMultPatterns, outputTerm) }

    /*
    * TODO (Joseph Bakouny): consider moving recordProjections out of AbstractTerm to allow the use:
    *  - of applicationProjection as arguments of other termApplications or explicitQualidApplications.
    *  - of explicitApplicationProjection as arguments of other termApplications or explicitQualidApplications.
    */
    private lazy val recordProjection: P[RecordProjection] = {
      lazy val explicitApplicationProjection: P[ExplicitApplicationProjection] =
        term ~ (".(" ~> explicitQualidApplication <~ ")") ^^ {
          case recordInstance ~ explicitQualidApp =>
            ExplicitApplicationProjection(recordInstance, explicitQualidApp)
        }
      lazy val applicationProjection: P[ApplicationProjection] =
        term ~ (".(" ~> termApplication <~ ")") ^^ {
          case recordInstance ~ termApp =>
            ApplicationProjection(recordInstance, termApp)
        }
      lazy val simpleProjection: P[SimpleProjection] =
        term ~ (".(" ~> qualid <~ ")") ^^ {
          case recordInstance ~ fieldName => SimpleProjection(recordInstance, fieldName)
        }
      (
        explicitApplicationProjection
        | applicationProjection
        | simpleProjection)
    }
    private lazy val recordInstantiation: P[RecordInstantiation] = {
      "{|" ~> repsep(concreteRecordField, ";") <~ "|}" ^^ {
        RecordInstantiation(_)
      }
    }

    private lazy val annotation: P[Annotation] = fixAnnotation | funAnnotation

    private lazy val fixAnnotation: P[FixAnnotation] = {
      "{" ~ "struct" ~> identifier <~ "}" ^^ { case id @ Ident(_) => FixAnnotation(id) }
    }

    private lazy val funAnnotation: P[FunAnnotation] = {
      "{" ~ "measure" ~> ("(" ~> fun <~ ")") ~ identifier <~ "}" ^^ {
        case anonFun ~ id => FunAnnotation(anonFun, id)
      }
    }
  }

  private object Term extends AbstractTerm {

    override protected lazy val termApplication: P[UncurriedTermApplication] =
      term ~ (argument +) ^^ { case term ~ arguments => UncurriedTermApplication(term, arguments) }

    private lazy val argument: P[Argument] = (
      TermWithoutApplication.term ^^ { case term => Argument(None, term) }
      | "(" ~> identifier ~ ":=" ~ TermWithoutApplication.term <~ ")" ^^ { case ident ~ lex_:= ~ term => Argument(Some(ident), term) })
  }

  private object TermWithoutApplication extends AbstractTerm {
    override protected lazy val termApplication: P[UncurriedTermApplication] = failure("termApplication is not a valid production for the object CoqParser.TermWithoutApplication")
  }

  private abstract class AbstractPattern {

    lazy val pattern: P[Pattern] = (
      infixPattern
      | constructorPattern
      | qualidPattern
      | underscorePattern
      | numberPattern
      | parenthesisOrPattern)

    //TODO (Joseph Bakouny): Consider a more elegant representation of infix patterns
    /*
     * Warning:
     * Infix patterns are not represented in the official Coq grammar
     * Infix patterns are currently only used for the list cons operator "::"
     */
    private lazy val infixPattern: P[InfixPattern] =
      pattern ~ "::" ~ pattern ^^ { case left ~ op ~ right => InfixPattern(left, op, right) }

    protected def constructorPattern: P[ConstructorPattern];

    private lazy val qualidPattern: P[QualidPattern] =
      qualid ^^ { QualidPattern(_) }

    private lazy val underscorePattern: P[Pattern] =
      "_" ^^^ UnderscorePattern

    private lazy val numberPattern: P[NumberPattern] =
      numberLiteral ^^ { NumberPattern(_) }

    private lazy val parenthesisOrPattern: P[ParenthesisOrPattern] =
      "(" ~> rep1sep(orPattern, ",") <~ ")" ^^ { ParenthesisOrPattern(_) }
  }

  private object Pattern extends AbstractPattern {

    protected lazy val constructorPattern: P[ConstructorPattern] =
      qualid ~ (PatternWithoutConstructor.pattern +) ^^ { case id ~ patterns => ConstructorPattern(id, patterns) }

  }

  private object PatternWithoutConstructor extends AbstractPattern {

    protected lazy val constructorPattern: P[ConstructorPattern] =
      failure("constructorPattern is not a valid production for the object CoqParser.PatternWithoutConstructor")

  }
}
