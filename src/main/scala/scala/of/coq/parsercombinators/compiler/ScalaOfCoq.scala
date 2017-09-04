package scala.of.coq.parsercombinators.compiler

import treehugger.forest._
import definitions._
import treehuggerDSL._

import scala.of.coq.parsercombinators.parser.Argument
import scala.of.coq.parsercombinators.parser.BetweenParenthesis
import scala.of.coq.parsercombinators.parser.Binders
import scala.of.coq.parsercombinators.parser.CoqAST
import scala.of.coq.parsercombinators.parser.Definition
import scala.of.coq.parsercombinators.parser.FixBody
import scala.of.coq.parsercombinators.parser.Fixpoint
import scala.of.coq.parsercombinators.parser.Ident
import scala.of.coq.parsercombinators.parser.Inductive
import scala.of.coq.parsercombinators.parser.InductiveBody
import scala.of.coq.parsercombinators.parser.InductiveBodyItem
import scala.of.coq.parsercombinators.parser.InfixOperator
import scala.of.coq.parsercombinators.parser.MatchItem
import scala.of.coq.parsercombinators.parser.Name
import scala.of.coq.parsercombinators.parser.Number
import scala.of.coq.parsercombinators.parser.Qualid
import scala.of.coq.parsercombinators.parser.Term
import scala.of.coq.parsercombinators.parser.Term_->
import scala.of.coq.parsercombinators.parser.UncurriedTermApplication
import scala.of.coq.parsercombinators.parser.Match
import scala.of.coq.parsercombinators.parser.PatternEquation
import scala.of.coq.parsercombinators.parser.Pattern
import scala.of.coq.parsercombinators.parser.MultPattern
import scala.of.coq.parsercombinators.parser.QualidPattern
import scala.of.coq.parsercombinators.parser.ConstructorPattern
import scala.of.coq.parsercombinators.parser.UnderscorePattern
import scala.of.coq.parsercombinators.parser.NumberPattern
import scala.of.coq.parsercombinators.parser.OrPattern
import scala.of.coq.parsercombinators.parser.ParenthesisOrPattern
import scala.of.coq.parsercombinators.parser.ExplicitSimpleBinder
import scala.of.coq.parsercombinators.parser.ExplicitBinderWithType
import scala.of.coq.parsercombinators.parser.ImplicitBinder
import scala.of.coq.parsercombinators.parser.ExplicitQualidApplication
import scala.of.coq.parsercombinators.parser.Sentence
import scala.of.coq.parsercombinators.parser.Assertion
import scala.of.coq.parsercombinators.parser.TermIf
import scala.of.coq.parsercombinators.parser.RequireImport
import scala.of.coq.parsercombinators.parser.InfixPattern
import scala.of.coq.parsercombinators.parser.ArgumentsCommand
import scala.of.coq.parsercombinators.parser.Type
import scala.of.coq.parsercombinators.parser.TupleValue
import scala.of.coq.parsercombinators.parser.ScopeCommand
import scala.of.coq.parsercombinators.parser.Fun
import scala.of.coq.parsercombinators.parser.LetConstructorArgsIn
import scala.of.coq.parsercombinators.parser.LetPatternIn
import scala.of.coq.parsercombinators.parser.SimpleLetIn

class ScalaOfCoq(curryingStrategy: CurryingStrategy) {

  def toTreeHuggerAst(coqAst: Sentence): List[Tree] = coqAst match {

    case RequireImport(_) | ArgumentsCommand(_, _) | ScopeCommand(_, _) =>
      List() // The above commands do not generate any Scala code
    case Definition(id, binders, Some(Type), bodyTypeTerm) =>
      List(createTypeAliasDefinition(id, binders) := coqTypeToTreeHuggerType(bodyTypeTerm))
    case Definition(id, binders, typeTerm, bodyTerm) =>
      List(createDefinition(typeTerm, id, binders) := termToTreeHuggerAst(bodyTerm))
    case Inductive(InductiveBody(Ident(parentName), parentBinders, _, indBodyItems)) =>
      /*
       * TODO (Jospeh Bakouny): This case clause ignores the type term.
       * Check what needs to be done with the type Term in future version
       */
      createCaseClassHierarchy(parentBinders, parentName, indBodyItems)
    case Fixpoint(FixBody(id, binders, _, typeTerm, bodyTerm)) =>
      // NOTE(Joseph Bakouny): Struct annotations should be ignored in Scala
      List(createDefinition(typeTerm, id, Some(binders)) := termToTreeHuggerAst(bodyTerm))
    case Assertion(_, id, binders, bodyTerm) =>
      List()
    case anythingElse =>
      throw new IllegalStateException("The following Coq AST is not supported: " + anythingElse.toCoqCode);
  }

  def toTreeHuggerAst(coqTrees: List[Sentence]): List[Tree] = coqTrees.flatMap(t => toTreeHuggerAst(t))

  def toScalaCode(coqTrees: List[Sentence]): String = toTreeHuggerAst(coqTrees).map(treeToString(_)).mkString("\n")

  def createObjectFileCode(objectName: String, coqTrees: List[Sentence]): String = {
    "import scala.of.coq.lang._\n" +
      "import Nat._\n" +
      "import MoreLists._\n" +
      createObjectFileCodeWithoutDependantClasses(objectName, coqTrees)
  }

  def createObjectFileCodeWithoutDependantClasses(objectName: String, coqTrees: List[Sentence]): String = {
    treeToString(OBJECTDEF(objectName) := BLOCK(toTreeHuggerAst(coqTrees)))
  }

  private def termToScalaCode(t: Term): String = treeToString(termToTreeHuggerAst(t))

  private def termToTreeHuggerAst(t: Term): Tree = t match {
    case BetweenParenthesis(UncurriedTermApplication(functionTerm, arguments)) =>
      createApplication(functionTerm, arguments)
    case Fun(binders, bodyTerm) =>
      createAnonymousFunction(binders, bodyTerm)
    case SimpleLetIn(Ident(id), binders, typeTerm, inputTerm, mainTerm) =>
      BLOCK(
        typeTerm.fold(VAL(id))(t => VAL(id, coqTypeToTreeHuggerType(t))) :=
          binders.fold(termToTreeHuggerAst(inputTerm))(createAnonymousFunction(_, inputTerm)),
        termToTreeHuggerAst(mainTerm)
      )
    case LetConstructorArgsIn(names, _, inputTerm, mainTerm) =>
      // TODO(Joseph Bakouny): consider supporting inductives with one constructor that are not tuples
      BLOCK(
        VAL(convertTuple(names, PatternUtils.convertNameToPatternVar)) :=
          termToTreeHuggerAst(inputTerm),
        termToTreeHuggerAst(mainTerm)
      )
    case LetPatternIn(pattern, inputTerm, _, mainTerm) =>
      BLOCK(
        VAL(PatternUtils.convertPattern(pattern)) :=
          termToTreeHuggerAst(inputTerm),
        termToTreeHuggerAst(mainTerm)
      )
    case TermIf(conditionTerm, _, thenTerm, elseTerm) =>
      IF(termToTreeHuggerAst(conditionTerm)).THEN(termToTreeHuggerAst(thenTerm)).ELSE(termToTreeHuggerAst(elseTerm))
    case UncurriedTermApplication(functionTerm, arguments) =>
      createApplication(functionTerm, arguments)
    case InfixOperator(leftOp, op, rightOp) => createInfixOperator(leftOp, convertToScalaInfixOperator(op), rightOp)
    case patternMatch @ Match(_, _, _) =>
      PatternUtils.convertPatternMatch(patternMatch)
    case Qualid(List(Ident(primitiveValue))) if qualidIsPrimitiveValueInScala(primitiveValue) =>
      convertQualitToPrimitiveValue(primitiveValue)
    case Qualid(xs) =>
      REF(xs.map { case Ident(name) => convertValue(name) }.mkString("."))
    case Number(n) =>
      LIT(n)
    case BetweenParenthesis(term) =>
      PAREN(termToTreeHuggerAst(term))
    case TupleValue(tupleTerms) =>
      convertTuple(tupleTerms, termToTreeHuggerAst)
    case anythingElse =>
      throw new IllegalStateException("The following Coq term is not supported: " + anythingElse.toCoqCode);
  }

  private def coqTypeToScalaCode(typeTerm: Term): String = treeToString(coqTypeToTreeHuggerType(typeTerm))

  private def coqTypeToTreeHuggerType(typeTerm: Term): Type = typeTerm match {
    case UncurriedTermApplication(genericTypeTerm, arguments) =>
      createTypeWithGenericParams(coqTypeToTreeHuggerType(genericTypeTerm), arguments.map {
        case Argument(_, typeTerm) => coqTypeToTreeHuggerType(typeTerm)
      })
    case ExplicitQualidApplication(id, genericTypeParams) =>
      createTypeWithGenericParams(coqTypeToTreeHuggerType(id), genericTypeParams.map(coqTypeToTreeHuggerType(_)))
    case Term_->(typeTerm1, typeTerm2) =>
      // TODO (Joseph Bakouny): Coq -> in lemmas can have a different significance, check how this can be supported if needed ?
      TYPE_REF(coqTypeToTreeHuggerType(typeTerm1)).TYPE_=>(TYPE_REF(coqTypeToTreeHuggerType(typeTerm2)))
    case Qualid(xs) =>
      TYPE_REF(xs.map { case Ident(name) => convertType(name) }.mkString("."))
    case BetweenParenthesis(term) =>
      coqTypeToTreeHuggerType(term)
    case tupleDef @ InfixOperator(leftTerm, "*", rightTerm) =>
      def allTupleTypesIn(t: Term): List[Type] = t match {
        case InfixOperator(t1, "*", t2) => allTupleTypesIn(t1) ::: allTupleTypesIn(t2)
        case typeTerm                   => List(coqTypeToTreeHuggerType(typeTerm))
      }
      TYPE_TUPLE(allTupleTypesIn(tupleDef))
    case anythingElse =>
      throw new IllegalStateException("The following Coq type is not supported: " + anythingElse.toCoqCode);
  }

  private def createApplication(functionTerm: Term, arguments: List[Argument]): Tree =
    {
      /*
     * Note (Joseph Bakouny): The Coq syntax "(ident := term)" should not be converted to Scala named arguments
     * since Coq only allows the application of this syntax to implicit parameters.
     * It should also be noted that implicit paremeters are currently converted to generics in Scala.
     */
      curryingStrategy.createApplication(
        termToTreeHuggerAst(functionTerm),
        arguments.map {
          case Argument(None, BetweenParenthesis(argValue)) => termToTreeHuggerAst(argValue) // remove parenthesis since they are not needed in Scala
          case Argument(None, argValue)                     => termToTreeHuggerAst(argValue)
          case Argument(Some(Ident(argName)), argValue)     => REF(argName) := termToTreeHuggerAst(argValue)
        }
      )
    }

  private def convertToScalaInfixOperator(coqOp: String): String = coqOp match {
    case "<=?"            => "<="
    case "<?"             => "<"
    case "=?"             => "=="
    case anyOtherOperator => anyOtherOperator
  }

  private def toNat(inputValue: Int): Tree = inputValue match {
    case 0            => REF("Zero")
    case n if (n > 0) => REF("S") APPLY toNat(n - 1)
    case n if (n < 0) => throw new IllegalStateException("Only Coq natural numbers are currently supported, the following negative number is, therefore, illegal: " + n)
  }

  private def qualidIsPrimitiveValueInScala(inputValue: String): Boolean = inputValue match {
    case "True"       => true
    case "true"       => true
    case "False"      => true
    case "false"      => true
    case anythingElse => false
  }

  private def convertQualitToPrimitiveValue(inputValue: String) = inputValue match {
    case "True"       => LIT(true)
    case "true"       => LIT(true)
    case "False"      => LIT(false)
    case "false"      => LIT(false)
    // The code should never get here!
    case anythingElse => throw new IllegalStateException("This qualid is not a primitive value in Scala: " + anythingElse)
  }

  private def convertValue(inputValue: String): String = inputValue match {
    case "cons"         => "Cons"
    // TODO (Joseph Bakouny): Leon "Nil" lists are written like this "Nil()" in pattern matches, check how to support this
    case "nil"          => "Nil"
    case "pair"         => "Tuple2"
    case anyOtherString => anyOtherString
  }

  private def convertType(inputType: String): String = inputType match {
    case "Z"            => "BigInt"
    case "nat"          => "Nat"
    case "list"         => "List"
    case "option"       => "Option"
    case "bool"         => "Boolean"
    case anyOtherString => anyOtherString
  }

  private def createAnonymousFunction(binders: Binders, bodyTerm: Term) = {
    def convertNamesToAnonFunParams(names: List[Name], optionalTypeTerm: Option[Term]) =
      names.map(name =>
        mkTreeFromDefStart(
          name match {
            case Name(Some(Ident(nameString))) =>
              optionalTypeTerm.fold {
                PARAM(nameString)
              } {
                (typeTerm: Term) =>
                  PARAM(nameString, coqTypeToTreeHuggerType(typeTerm))
              }
            case Name(None) => PARAM(WILDCARD)
          }
        )
      )

    val Binders(bindersList) = binders;
    val params = bindersList.flatMap {
      case ExplicitSimpleBinder(name)              => convertNamesToAnonFunParams(List(name), None)
      case ExplicitBinderWithType(names, typeTerm) => convertNamesToAnonFunParams(names, Some(typeTerm))
      case ImplicitBinder(_, _) =>
        throw new IllegalStateException(
          "The implicit parameters of this anonymous function cannot be converted to Scala: " +
            Fun(binders, bodyTerm).toCoqCode)
    }

    curryingStrategy.createAnonymousFunction(params, termToTreeHuggerAst(bodyTerm))
  }

  private def createTypeAliasDefinition(id: Ident, binders: Option[Binders]) = {
    val typeParams = convertTypeBindersToTypeVars(binders)
    val Ident(nameString) = id
    TYPEVAR(nameString).withTypeParams(typeParams)
  }

  private def createDefinition(typeTerm: Option[Term], id: Ident, binders: Option[Binders]): DefTreeStart = {
    val declaration: DefTreeStart = typeTerm.fold(DEFINFER(id.toCoqCode)) {
      typeTerm => DEF(id.toCoqCode, coqTypeToTreeHuggerType(typeTerm))
    }

    binders.fold(declaration) {
      binders =>
        val (typeDefs, paramDefs) = partitionParams(binders)

        curryingStrategy.createDefinition(
          declaration.withTypeParams(typeDefs),
          paramDefs
        )
    }
  }

  private def createCaseClassHierarchy(parentBinders: Option[Binders], parentName: String, indBodyItems: List[InductiveBodyItem]) = {
    val parentTypeDefs = convertTypeBindersToTypeVars(parentBinders)

    val parentDeclaration: Tree =
      CLASSDEF(parentName)
        .withTypeParams(parentTypeDefs)
        .withFlags(Flags.SEALED)
        .withFlags(Flags.ABSTRACT)
        .tree

    val caseClassHierarchy: List[Tree] =
      indBodyItems flatMap {
        /*
         * TODO (Jospeh Bakouny): This case clause ignores the type term.
         * Check what needs to be done with the type Term in future version
         */
        case InductiveBodyItem(Ident(name), binders, _) =>
          binders.fold {
            /*
             *   TODO(Joseph Bakouny): Fix the empty case class issue:
             *   An empty case class is not generated with the correct parenthesis "()".
             *
             *   This is probably an issue with treehugger.scala.
             */
            val caseObjectDeclaration: Tree =
              CASEOBJECTDEF(name)
                .withParents(parentName)
                .tree

            List(caseObjectDeclaration)
          } {
            binders =>
              val (typeDefs, paramsDefs) = partitionParams(binders)

              val caseClassDeclaration: Tree =
                CASECLASSDEF(name)
                  .withTypeParams(parentTypeDefs ::: typeDefs)
                  .withParams(paramsDefs)
                  .withParents(createTypeWithGenericParams(parentName, parentTypeDefs.map(typeVar => TYPE_REF(typeVar.name))))
                  .tree

              val optionalCompanion =
                curryingStrategy.createCompanionObject(name, parentTypeDefs ::: typeDefs, paramsDefs)

              caseClassDeclaration ::
                optionalCompanion.fold[List[Tree]](Nil)(o => List(o))
          }
      }

    parentDeclaration :: caseClassHierarchy
  }

  private def partitionParams(binders: Binders): (List[TypeDefTreeStart], List[ValDef]) = {
    val Binders(bindersList) = binders;

    val (typeParams, params) = bindersList.partition {
      /*
       *  TODO (Jospeh Bakouny): The partitioning algorithm between typeParams and params can be improved.
       *  In fact, in future versions, it might not be necessary to consider all implicit parameters as type params.
       *  Consider supporting converting implicit non-type params to Scala implicits.
       */
      case ImplicitBinder(_, _)         => true
      case ExplicitBinderWithType(_, _) => false
      case anythingElse =>
        throw new IllegalStateException("The following parameter notation is not supported: " + anythingElse.toCoqCode);
    }

    val implicitBinders: List[TypeDefTreeStart] =
      for {
        ImplicitBinder(names, _) <- typeParams
        Name(Some(Ident(nameString))) <- names
      } yield TYPEVAR(nameString)

    // TODO (Joseph Bakouny): Should we take currying into consideration ?
    val paramsDefs: List[ValDef] =
      for {
        ExplicitBinderWithType(names, typeTerm) <- params
        // TODO (Joseph Bakouny): Should we ignore names with the pattern "Name(None)"?
        Name(Some(Ident(nameString))) <- names
      } yield {
        mkTreeFromDefStart(PARAM(nameString, coqTypeToTreeHuggerType(typeTerm)))
      }

    (implicitBinders, paramsDefs)
  }

  private def convertTypeBindersToTypeVars(typeBinders: Option[Binders]) =
    typeBinders.fold(List[TypeDefTreeStart]()) {
      case Binders(binders) =>
        def convertNamesToTypeVars(names: List[Name]) =
          for { Name(Some(Ident(nameString))) <- names } yield TYPEVAR(nameString)
        binders.flatMap {
          case ExplicitSimpleBinder(name)          => convertNamesToTypeVars(List(name))
          case ExplicitBinderWithType(names, Type) => convertNamesToTypeVars(names)
          case ImplicitBinder(names, None)         => convertNamesToTypeVars(names)
          case ImplicitBinder(names, Some(Type))   => convertNamesToTypeVars(names)
          case anythingElse =>
            throw new IllegalStateException("The following Coq type parameter is not supported: " + anythingElse)
        }
    }

  private def createTypeWithGenericParams(typeName: Type, genericTypeParams: List[Type]): Type = {
    typeName.TYPE_OF(genericTypeParams)
  }

  private def createInfixOperator(leftOp: Term, op: String, rightOp: Term) = {
    termToTreeHuggerAst(leftOp).INFIX(op).APPLY(termToTreeHuggerAst(rightOp))
  }

  private def convertTuple[A, B <: Tree](tupleElems: List[A], converterFunction: A => B): Tree = {
    tupleElems match {
      case Nil      => throw new IllegalStateException("Cannot convert a tuple with no elements!")
      case p :: Nil => converterFunction(p) // A tuple with a single element is just a value
      case p :: ps  => TUPLE(tupleElems.map(converterFunction))
    }
  }

  private object PatternUtils {

    def convertPatternMatch(patternMatch: Match) = {
      // TODO(Joseph Bakouny): Check if the return type of the match should always be ignored
      val Match(matchItems, _, equations) = patternMatch
      convertTuple(matchItems, convertMatchItem).MATCH(equations.map(convertPatternEquation))
    }

    def convertPattern(coqPattern: Pattern): Tree = coqPattern match {
      /*
     * TODO (Joseph Bakouny):
     * Infix patterns are currently only used for the list cons operator
     * Check if there is another usage that should be implemented.
     */
      case InfixPattern(head, "::", tail)        => convertPattern(head) UNLIST_:: (convertPattern(tail))
      case ConstructorPattern(constructor, args) => termToTreeHuggerAst(constructor).UNAPPLY(args.map(convertPattern))
      case QualidPattern(q)                      => termToTreeHuggerAst(q)
      case UnderscorePattern                     => WILDCARD
      /*
       * TODO (Joseph Bakouny): Handle Nats in pattern position correctly
       * Generate numbers such as 3 and not S(S(S(Zero))))
       * For this, consider subclassing BigInt and implementing unapply.
       */
      case NumberPattern(Number(n))              => toNat(n)
      case ParenthesisOrPattern(orPatterns)      => convertTuple(orPatterns, convertOrPattern)
      case anythingElse =>
        throw new IllegalStateException("The following Coq pattern is not yet supported: " + anythingElse.toCoqCode);
    }

    def convertNameToPatternVar(name: Name) =
      name match {
        case Name(None)            => WILDCARD
        case Name(Some(Ident(id))) => ID(id)
      }

    private def convertMatchItem(matchItem: MatchItem): Tree = matchItem match {
      case MatchItem(coqTerm, None, None) => termToTreeHuggerAst(coqTerm)
      case anythingElse                   => throw new IllegalStateException("The following Coq match item is not supported: " + anythingElse.toCoqCode)
    }

    private def convertPatternEquation(patternEquation: PatternEquation) =
      {
        val PatternEquation(multPatterns, outputTerm) = patternEquation
        CASE(
          multPatterns.map(convertMultPattern).reduce(_ OR_PATTERN _)
        ) ==> termToTreeHuggerAst(outputTerm)
      }

    private def convertMultPattern(multPattern: MultPattern): Tree = {
      val MultPattern(patterns) = multPattern
      convertTuple(patterns, convertPattern)
    }

    private def convertOrPattern(orPattern: OrPattern) = {
      val OrPattern(patterns) = orPattern
      patterns.map(convertPattern).reduce(_ OR_PATTERN _)
    }
  }
}
