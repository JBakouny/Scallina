package scala.of.coq.parsercombinators.parser

import scala.util.parsing.input.Positional

sealed trait CoqAST {
  def toCoqCode: String
}

// Start of sentence
sealed trait Sentence extends CoqAST

//TODO (Joseph Bakouny): This AST is not in the grammar, consider a more in-depth support for modules.
case class RequireImport(moduleName: Qualid, shouldExport: Boolean = false) extends Sentence {
  def toCoqCode: String = "Require " + (if (shouldExport) "Export" else "Import") + " " + moduleName.toCoqCode + "."
}

case class LoadCommand(moduleName: Qualid) extends Sentence {
  def toCoqCode: String = "Load " + moduleName.toCoqCode + "."
}

case class SetCommand(flag: String) extends Sentence {
  def toCoqCode: String = "Set " + flag + "."
}

/*
 *  NOTE: This AST node is not in the grammar, it supports the commands of the form:
 *  Arguments Leaf {A} _.
 *  Arguments Node {A} _ _.
 */
case class ArgumentsCommand(id: Qualid, args: Binders) extends Sentence {
  def toCoqCode: String = "Arguments " + id.toCoqCode + " " + args.toCoqCode + "."
}

/*
 *  NOTE: This AST node is not in the grammar, it supports the commands of the form:
 *  Local Open Scope Z_scope.
 *  or
 *  Open Scope Z_scope.
 */
case class ScopeCommand(scopeName: Qualid, isLocal: Boolean) extends Sentence {
  def toCoqCode: String = (if (isLocal) "Local" else "") + "Open Scope " + scopeName.toCoqCode + "."
}

/*
 * TODO (Joseph Bakouny): Add [Local] keyword and "Let" production to Definition in subsequent versions
 */
case class Definition(ident: Ident, binders: Option[Binders], typeTerm: Option[Term], bodyTerm: Term) extends Sentence {
  def toCoqCode: String =
    "Definition " + ident.toCoqCode +
      binders.fold("")(" " + _.toCoqCode) +
      typeTerm.fold("")(" : " + _.toCoqCode) +
      " := " + bodyTerm.toCoqCode + "."
}

// TODO (Joseph Bakouny): Consider supporting list of fixBodies for a Fixpoint and also CoFixpoint
case class Fixpoint(fixBody: FixBody) extends Sentence {
  def toCoqCode: String = "Fixpoint " + fixBody.toCoqCode + "."
}

case class FunctionDef(functionBody: FunctionBody) extends Sentence {
  def toCoqCode: String = "Function " + functionBody.toCoqCode + "."
}

case class Record(
  keyword:     RecordKeyword,
  id:          Ident,
  params:      Option[Binders],
  sort:        Option[Sort],
  constructor: Option[Ident],
  fields:      List[RecordField]) extends Sentence {

  def toCoqCode: String =
    keyword.toCoqCode + " " + id.toCoqCode +
      params.fold("")(" " + _.toCoqCode) +
      sort.fold("")(" : " + _.toCoqCode) + " :=\n" +
      constructor.fold("")(_.toCoqCode + " ") +
      "{\n" +
      fields.map(_.toCoqCode).mkString(";\n") +
      "\n}."
}

case class RecordInstantiation(fields: List[ConcreteRecordField]) extends Term {
  def toCoqCode = "{|\n" +
    fields.map(_.toCoqCode).mkString(";\n") +
    "\n|}"
}

// Start of RecordKeyword
sealed trait RecordKeyword extends CoqAST

case object RecordKeyword extends RecordKeyword {
  def toCoqCode: String = "Record"
}

case object StructureKeyword extends RecordKeyword {
  def toCoqCode: String = "Structure"
}

case object InductiveRecordKeyword extends RecordKeyword {
  def toCoqCode: String = "Inductive"
}

case object CoInductiveRecordKeyword extends RecordKeyword {
  def toCoqCode: String = "CoInductive"
}
// End of RecordKeyword

// Start of RecordField
sealed abstract class RecordField(name: Name, binders: Option[Binders]) extends CoqAST {
  def toCoqCode: String = name.toCoqCode + binders.fold("")(" " + _.toCoqCode)
}

case class AbstractRecordField(name: Name, binders: Option[Binders], typeTerm: Term) extends RecordField(name, binders) {
  override def toCoqCode: String = super.toCoqCode + " : " + typeTerm.toCoqCode
}

case class ConcreteRecordField(name: Name, binders: Option[Binders], typeTerm: Option[Term], bodyTerm: Term) extends RecordField(name, binders) {
  override def toCoqCode: String = super.toCoqCode + typeTerm.fold("")(" : " + _.toCoqCode) + " := " + bodyTerm.toCoqCode
}
// End of RecordField

case class Assertion(keyword: AssertionKeyword, id: Ident, binders: Option[Binders], term: Term) extends Sentence {
  def toCoqCode: String =
    keyword.toCoqCode + " " + id.toCoqCode +
      " " + binders.fold("")(_.toCoqCode) +
      ": " + term.toCoqCode + "."
}

// Start of AssertionKeyword
sealed trait AssertionKeyword extends CoqAST

case object Theorem extends AssertionKeyword {
  def toCoqCode: String = "Theorem"
}

case object Lemma extends AssertionKeyword {
  def toCoqCode: String = "Lemma"
}

case object Remark extends AssertionKeyword {
  def toCoqCode: String = "Remark"
}

case object Fact extends AssertionKeyword {
  def toCoqCode: String = "Fact"
}

case object Corollary extends AssertionKeyword {
  def toCoqCode: String = "Corollary"
}

case object Proposition extends AssertionKeyword {
  def toCoqCode: String = "Proposition"
}

case object DefinitionAssertionKeyword extends AssertionKeyword {
  def toCoqCode: String = "Definition"
}

case object Example extends AssertionKeyword {
  def toCoqCode: String = "Example"
}
// End of AssertionKeyword

// Start of Proof
sealed trait Proof extends CoqAST

case object ProofQed extends Proof {
  def toCoqCode: String = "Proof. ... Qed."
}

case object ProofDefined extends Proof {
  def toCoqCode: String = "Proof. ... Defined."
}

case object ProofAdmitted extends Proof {
  def toCoqCode: String = "Proof. ... Admitted."
}
// End of Proof

// TODO (Joseph Bakouny): Consider supporting a list of inductive bodies and CoInductives
case class Inductive(indBody: InductiveBody) extends Sentence {
  def toCoqCode: String = "Inductive " + indBody.toCoqCode + "."
}

// End of sentence

// TODO (Joseph Bakouny): Check why the InductiveBody typeTerm seems optional in Coq but marked as required in the grammar
case class InductiveBody(id: Ident, binders: Option[Binders], typeTerm: Option[Term], indBodyItems: List[InductiveBodyItem]) extends CoqAST {
  def toCoqCode: String =
    id.toCoqCode + binders.fold("")(" " + _.toCoqCode) + typeTerm.fold("")(" : " + _.toCoqCode) + " :=\n" +
      indBodyItems.map(_.toCoqCode).mkString("\n| ")
}

/**
 * This is just a helper case class used in the case class InductiveBody, it is not present in the original grammar.
 */
case class InductiveBodyItem(id: Ident, binders: Option[Binders], typeTerm: Option[Term]) extends CoqAST {
  def toCoqCode: String = id.toCoqCode + binders.fold("")(" " + _.toCoqCode) + typeTerm.fold("")(" : " + _.toCoqCode)
}

// Start of term
sealed trait Term extends CoqAST

case class ForAll(binders: Binders, term: Term) extends Term {
  def toCoqCode: String = "forall " + binders.toCoqCode + ", " + term.toCoqCode
}

case class Fun(binders: Binders, term: Term) extends Term {
  def toCoqCode: String =
    "fun " + binders.toCoqCode + " => " + term.toCoqCode
}

case class Fix(fixBodies: FixBodies) extends Term {
  def toCoqCode: String = "fix " + fixBodies.toCoqCode
}

// Start of LetIn
sealed trait LetIn extends Term

case class SimpleLetIn(indentifier: Ident, binders: Option[Binders], typeTerm: Option[Term], inputTerm: Term, mainTerm: Term) extends LetIn {
  def toCoqCode: String =
    "let " + indentifier.toCoqCode +
      binders.fold("")(" " + _.toCoqCode) +
      typeTerm.fold("")(" : " + _.toCoqCode) +
      " := " + inputTerm.toCoqCode +
      " in " + mainTerm.toCoqCode
}

case class LetFixIn(fixBody: FixBody, mainTerm: Term) extends LetIn {
  def toCoqCode: String =
    "let fix " + fixBody.toCoqCode +
      " in " + mainTerm.toCoqCode
}

case class LetConstructorArgsIn(names: List[Name], depType: Option[DepRetType], inTerm: Term, mainTerm: Term) extends LetIn {
  def toCoqCode: String =
    "let (" + names.map(_.toCoqCode).mkString(", ") + ")" +
      depType.fold("")(" " + _.toCoqCode) +
      " := " + inTerm.toCoqCode + " in " + mainTerm.toCoqCode
}

case class LetPatternIn(pattern: Pattern, inputTerm: Term, returnType: Option[ReturnType], mainTerm: Term) extends LetIn {
  def toCoqCode: String =
    "let ' " + pattern.toCoqCode +
      " := " + inputTerm.toCoqCode +
      returnType.fold("")(" " + _.toCoqCode) +
      " in " + mainTerm.toCoqCode
}

// End of LetIn

case class TermIf(cond: Term, depRetType: Option[DepRetType], thenPart: Term, elsePart: Term) extends Term {
  def toCoqCode: String =
    "if " + cond.toCoqCode +
      depRetType.fold("")(" " + _.toCoqCode) +
      " then " + thenPart.toCoqCode +
      " else " + elsePart.toCoqCode
}

case class Term_:(termA: Term, termB: Term) extends Term {
  def toCoqCode: String = termA.toCoqCode + " : " + termB.toCoqCode
}

case class Term_<:(termA: Term, termB: Term) extends Term {
  def toCoqCode: String = termA.toCoqCode + " <: " + termB.toCoqCode
}

case class Term_:>(term: Term) extends Term {
  def toCoqCode: String = term.toCoqCode + " :> "
}

case class Term_->(termA: Term, termB: Term) extends Term {
  def toCoqCode: String = termA.toCoqCode + " -> " + termB.toCoqCode
}

// Start of TermApplication
sealed trait TermApplication extends Term {
  /*
   * TODO (Joseph Bakouny): In case this functionality is really needed, this method should be modified to be
   * applied recursively on all subterms, this will require a case clause for most case classes.
   */
  def currify: TermApplication = this match {
    case UncurriedTermApplication(term, arg :: args) => (args foldLeft CurriedTermApplication(term, arg))((termApp, arg) => CurriedTermApplication(termApp, arg))
    case otherAst                                    => otherAst
  }
}

case class UncurriedTermApplication(term: Term, arguments: List[Argument]) extends TermApplication {
  def toCoqCode: String = term.toCoqCode + " " + (arguments.map(_.toCoqCode)).mkString(" ")
}

case class CurriedTermApplication(term: Term, argument: Argument) extends TermApplication {
  def toCoqCode: String = term.toCoqCode + " " + argument.toCoqCode
}
// End of TermApplication

case class ExplicitQualidApplication(id: Qualid, arguments: List[Term]) extends Term {
  def toCoqCode: String = "@ " + id.toCoqCode + (if (arguments.isEmpty) "" else " ") + (arguments.map(_.toCoqCode)).mkString(" ")
}

case class Term_%(term: Term, ident: Ident) extends Term {
  def toCoqCode: String = term.toCoqCode + " % " + ident.toCoqCode
}

/*
 * TODO (Joseph Bakouny): infix operators are not represented in the Coq grammar, this class should perhaps be re-thinked.
 */
case class InfixOperator(leftOperand: Term, operator: String, rightOperand: Term) extends Term {
  def toCoqCode: String = leftOperand.toCoqCode + " " + operator + " " + rightOperand.toCoqCode
}

case class Match(matchItems: List[MatchItem], returnType: Option[ReturnType], equations: List[PatternEquation]) extends Term {
  def toCoqCode: String =
    "match " + matchItems.map(_.toCoqCode).mkString(" , ") + returnType.fold("")(" " + _.toCoqCode) + " with\n" +
      equations.map(_.toCoqCode).mkString("\n| ") +
      "\nend"
}

case class Qualid(idents: List[Ident]) extends Term {
  def toCoqCode: String = idents.map(_.toCoqCode).mkString(".")
}

// Start of Sort
sealed trait Sort extends Term

case object Prop extends Sort {
  def toCoqCode: String = "Prop"
}

case object Set extends Sort {
  def toCoqCode: String = "Set"
}

case object Type extends Sort {
  def toCoqCode: String = "Type"
}
// End of Sort

case class Number(n: Int) extends Term {
  def toCoqCode: String = n.toString
}

/*
 * NOTE: This AST node is not in the grammar, it supports Coq tuple values of the form:
 * (k,v)
 */
case class TupleValue(tupleTerms: List[Term]) extends Term {
  def toCoqCode: String = tupleTerms match {
    case Nil     => "()"
    case t :: ts => "(" + ts.foldLeft(t.toCoqCode)(_ + ", " + _.toCoqCode) + ")"
  }
}

case class BetweenParenthesis(term: Term) extends Term {
  def toCoqCode: String = "(" + term.toCoqCode + ")"
}

// Start of RecordProjection
sealed abstract class RecordProjection(recordInstance: Term) extends Term {
  def toCoqCode: String = recordInstance.toCoqCode + ".("
}

case class SimpleProjection(recordInstance: Term, fieldName: Qualid) extends RecordProjection(recordInstance) {
  override def toCoqCode: String = super.toCoqCode + fieldName.toCoqCode + ")"
}

case class ApplicationProjection(recordInstance: Term, termApplication: TermApplication) extends RecordProjection(recordInstance) {
  override def toCoqCode: String = super.toCoqCode + termApplication.toCoqCode + ")"
}

case class ExplicitApplicationProjection(recordInstance: Term, explicitQualidApplication: ExplicitQualidApplication) extends RecordProjection(recordInstance) {
  override def toCoqCode: String = super.toCoqCode + " " + explicitQualidApplication.toCoqCode + ")"
}

// End of RecordProjection

// End of Term

case class Argument(identifier: Option[Ident], term: Term) extends CoqAST {
  def toCoqCode: String = {
    def termCoqCode = term.toCoqCode
    identifier.fold(termCoqCode)("(" + _.toCoqCode + " := " + termCoqCode + ")")
  }
}

case class Binders(binders: List[Binder]) extends CoqAST {
  def toCoqCode: String = binders.map(_.toCoqCode).mkString(" ")
}

// Start of Binder
sealed trait Binder extends CoqAST {
  def doOpenDelimiter: String
  def doCloseDelimiter: String
}

case class ExplicitSimpleBinder(name: Name) extends Binder {
  def doOpenDelimiter: String = ""
  def doCloseDelimiter: String = ""

  def toCoqCode: String = doOpenDelimiter + name.toCoqCode + doCloseDelimiter
}

// Start of BinderListGroup

// This abstract class is just used to refactor the toCoqCode method
sealed abstract class NameGroupBinder(names: List[Name], typeTerm: Option[Term]) extends Binder {
  def toCoqCode: String = doOpenDelimiter + names.map(_.toCoqCode).mkString(" ") + typeTerm.fold("")(" : " + _.toCoqCode) + doCloseDelimiter
}

case class ExplicitBinderWithType(names: List[Name], typeTerm: Term) extends NameGroupBinder(names, Some(typeTerm)) {
  def doOpenDelimiter: String = "("
  def doCloseDelimiter: String = ")"
}

/*
 * The ImplicitBinder case class represents implicit parameters (used, for example, the simulate generics).
 *
 * Although this is not specified in the official Coq grammar, it was added to this
 * implementation to be able to support notations such as the ones below:
 *
 * fun {A : Type} (l r : A) => l
 * fun {A} (l r : A) => l
 * fun {A B} (l : A) (r : B) => l
 *
 * The above notation supports the use of curly brackets {...}
 */
case class ImplicitBinder(names: List[Name], typeTerm: Option[Term]) extends NameGroupBinder(names, typeTerm) {
  def doOpenDelimiter: String = "{"
  def doCloseDelimiter: String = "}"
}

// End of BinderListGroup

// End of Binder

case class Name(name: Option[Ident]) extends CoqAST {
  def toCoqCode: String = name.fold("_")(_.toCoqCode)
}

case class Ident(name: String) extends CoqAST {
  def toCoqCode: String = name
}

/*
 * TODO (Joseph Bakouny): For the moment, we consider that a FixBodies only contains one fixBody.
 * In subsequent versions, FixBodies should contain a list of FixBody.
 */
case class FixBodies(fixBody: FixBody) extends Term {
  def toCoqCode: String = fixBody.toCoqCode
}

abstract sealed class RecursiveFunBody(ident: Ident, binders: Binders, annot: Option[Annotation], typeTerm: Option[Term], bodyTerm: Term)
  extends CoqAST {
  def toCoqCode: String =
    ident.toCoqCode + " " + binders.toCoqCode +
      annot.fold("")(" " + _.toCoqCode) +
      typeTerm.fold("")(" : " + _.toCoqCode) +
      " := " + bodyTerm.toCoqCode
}

case class FixBody(ident: Ident, binders: Binders, annotation: Option[FixAnnotation], typeTerm: Option[Term], bodyTerm: Term)
  extends RecursiveFunBody(ident, binders, annotation, typeTerm, bodyTerm)

case class FunctionBody(ident: Ident, binders: Binders, annotation: Annotation, typeTerm: Option[Term], bodyTerm: Term)
  extends RecursiveFunBody(ident, binders, Some(annotation), typeTerm, bodyTerm)

sealed trait Annotation extends CoqAST

case class FixAnnotation(ident: Ident) extends Annotation {
  def toCoqCode: String = "{ struct " + ident.toCoqCode + " }"
}

case class FunAnnotation(anonFun: Fun, ident: Ident) extends Annotation {
  def toCoqCode: String = "{ measure (" + anonFun.toCoqCode + ") " + ident.toCoqCode + " }"
}

/**
 * This is just a helper case class used in the case class MatchItem, it is not present in the original grammar.
 */
case class MatchItemPattern(id: Qualid, patterns: List[Pattern]) extends Pattern {
  def toCoqCode: String = id.toCoqCode + (if (patterns.isEmpty) "" else " ") + patterns.map(_.toCoqCode).mkString(" ");
}

case class MatchItem(term: Term, name: Option[Name], matchItemPattern: Option[MatchItemPattern]) extends CoqAST {
  def toCoqCode: String = term.toCoqCode + name.fold("")(" as " + _.toCoqCode) + matchItemPattern.fold("")(" in " + _.toCoqCode)
}

case class DepRetType(name: Option[Name], returnType: ReturnType) extends CoqAST {
  def toCoqCode: String = name.fold("")("as " + _.toCoqCode + " ") + returnType.toCoqCode
}

case class ReturnType(term: Term) extends CoqAST {
  def toCoqCode: String = "return " + term.toCoqCode
}

case class PatternEquation(orMultPatterns: List[MultPattern], outputTerm: Term) extends CoqAST {
  def toCoqCode: String = orMultPatterns.map(_.toCoqCode).mkString(" | ") + " => " + outputTerm.toCoqCode;
}

case class MultPattern(patterns: List[Pattern]) extends CoqAST {
  def toCoqCode: String = patterns.map(_.toCoqCode).mkString(" , ");
}

// Start of Pattern
sealed trait Pattern extends CoqAST

//TODO (Joseph Bakouny): Consider a more elegant representation of infix patterns
/*
 * Warning: infix patterns are not represented in the official Coq grammar!
 */
case class InfixPattern(left: Pattern, op: String, right: Pattern) extends Pattern {
  def toCoqCode: String = left.toCoqCode + " " + op + " " + right.toCoqCode;
}

case class ConstructorPattern(id: Qualid, patterns: List[Pattern]) extends Pattern {
  def toCoqCode: String = id.toCoqCode + " " + patterns.map(_.toCoqCode).mkString(" ");
}

case class QualidPattern(id: Qualid) extends Pattern {
  def toCoqCode: String = id.toCoqCode
}

case object UnderscorePattern extends Pattern {
  def toCoqCode: String = "_"
}

case class NumberPattern(num: Number) extends Pattern {
  def toCoqCode: String = num.toCoqCode
}

case class ParenthesisOrPattern(orPatterns: List[OrPattern]) extends Pattern {
  def toCoqCode: String = "(" + orPatterns.map(_.toCoqCode).mkString(", ") + ")"
}
//End of Pattern

case class OrPattern(patterns: List[Pattern]) extends CoqAST {
  def toCoqCode: String = patterns.map(_.toCoqCode).mkString(" | ")
}
