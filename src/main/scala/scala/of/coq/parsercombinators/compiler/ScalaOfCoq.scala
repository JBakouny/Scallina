package scala.of.coq.parsercombinators.compiler

import treehugger.forest
import treehugger.forest._
import treehuggerDSL._

import scala.of.coq.parsercombinators.compiler.RecordPreprocessor._
import scala.of.coq.parsercombinators.parser.{
  AbstractRecordField,
  Argument,
  ArgumentsCommand,
  Assertion,
  BetweenParenthesis,
  Binder,
  Binders,
  ConcreteRecordField,
  ConstructorPattern,
  Definition,
  ExplicitBinderWithType,
  ExplicitQualidApplication,
  ExplicitSimpleBinder,
  FixBody,
  Fixpoint,
  Fun,
  FunctionBody,
  FunctionDef,
  Ident,
  ImplicitBinder,
  Inductive,
  InductiveBody,
  InductiveBodyItem,
  InfixOperator,
  InfixPattern,
  LetConstructorArgsIn,
  LetPatternIn,
  LoadCommand,
  Match,
  MatchItem,
  MultPattern,
  Name,
  Number,
  NumberPattern,
  OrPattern,
  ParenthesisOrPattern,
  Pattern,
  PatternEquation,
  Qualid,
  QualidPattern,
  Record,
  RecordField,
  RecordInstantiation,
  RequireImport,
  ScopeCommand,
  Sentence,
  Set,
  SimpleLetIn,
  SimpleProjection,
  Term,
  TermIf,
  Term_->,
  TupleValue,
  Type,
  UncurriedTermApplication,
  UnderscorePattern
}

// TODO(Joseph Bakouny) restrict generics using Set instead of Type
class ScalaOfCoq(coqTrees: List[Sentence], curryingStrategy: CurryingStrategy) {

  def createObjectFileCode(objectName: String): String = {
    "import scala.of.coq.lang._\n" +
      "import Nat._\n" +
      "import Pairs._\n" +
      "import MoreLists._\n" +
      "import scala.concurrent.Future\n" +
      "import MoreFutures._\n" +
      createObjectFileCodeWithoutDependantClasses(objectName)
  }

  def createObjectFileCodeWithoutDependantClasses(
      objectName: String): String = {
    treeToString(OBJECTDEF(objectName) := BLOCK(toTreeHuggerAst(coqTrees)))
  }

  def generateScalaCode: String =
    toTreeHuggerAst(coqTrees).map(treeToString(_)).mkString("\n")

  private val constructorToRecordTypeFields =
    computeConstructorToRecordTypeFields(coqTrees)

  private def toTreeHuggerAst(coqTrees: List[Sentence]): List[Tree] =
    coqTrees.flatMap(t => toTreeHuggerAst(t))

  private def toTreeHuggerAst(coqAst: Sentence): List[Tree] = coqAst match {
    case RequireImport(_, _) | LoadCommand(_) | ArgumentsCommand(_, _) |
        ScopeCommand(_, _) =>
      List() // The above commands do not generate any Scala code
    case Definition(id, binders, Some(Set | Type), bodyTypeTerm) =>
      List(
        createTypeAliasDefinition(id, binders) := coqTypeToTreeHuggerType(
          bodyTypeTerm))
    case Definition(Ident(name),
                    args,
                    Some(Qualid(List(Ident(recordType)))),
                    RecordInstantiation(concreteRecordFields)) =>
      List(
        RecordUtils
          .convertRecordInstance(name, args, recordType, concreteRecordFields))
    case Definition(id, binders, typeTerm, bodyTerm) =>
      List(
        createDefinition(id, binders, typeTerm) := termToTreeHuggerAst(
          bodyTerm))
    case Inductive(
        InductiveBody(Ident(parentName), parentBinders, _, indBodyItems)) =>
      /*
       * TODO (Jospeh Bakouny): This case clause ignores the type term.
       * Check what needs to be done with the type Term in future version
       */
      createCaseClassHierarchy(parentBinders, parentName, indBodyItems)
    case Fixpoint(FixBody(id, binders, _, typeTerm, bodyTerm)) =>
      List(
        createDefinition(id, Some(binders), typeTerm) := termToTreeHuggerAst(
          bodyTerm))
    // NOTE(Joseph Bakouny): annotations should be ignored in Scala
    case FunctionDef(FunctionBody(id, binders, _, typeTerm, bodyTerm)) =>
      List(
        createDefinition(id, Some(binders), typeTerm) := termToTreeHuggerAst(
          bodyTerm))
    case record @ Record(_, _, _, None | Some(Type), _, _) =>
      RecordUtils.createTreeHuggerAstFromRecord(record)
    case Assertion(_, _, _, _) =>
      List()
    case anythingElse =>
      throw new IllegalStateException(
        "The following Coq AST is not supported: " + anythingElse.toCoqCode);
  }

  private def termToTreeHuggerAst(t: Term): Tree = t match {
    case BetweenParenthesis(
        UncurriedTermApplication(functionTerm, arguments)) =>
      createApplication(functionTerm, arguments)
    case Fun(binders, bodyTerm) =>
      createAnonymousFunction(binders, bodyTerm)
    case letIn @ (SimpleLetIn(_, _, _, _, _) |
        LetConstructorArgsIn(_, _, _, _) | LetPatternIn(_, _, _, _)) =>
      BLOCK(blockTermToTreeHuggerAstList(letIn))
    case TermIf(conditionTerm, _, thenTerm, elseTerm) =>
      IF(termToTreeHuggerAst(conditionTerm))
        .THEN(termToTreeHuggerAst(thenTerm))
        .ELSE(termToTreeHuggerAst(elseTerm))
    case UncurriedTermApplication(functionTerm, arguments) =>
      createApplication(functionTerm, arguments)
    case InfixOperator(leftOp, op, rightOp) =>
      createInfixOperator(leftOp, convertToScalaInfixOperator(op), rightOp)
    // TODO(Joseph Bakouny): Check if the return type of the match should always be ignored
    case patternMatch @ Match(_, None, _) =>
      PatternUtils.convertPatternMatch(patternMatch)
    case SimpleProjection(recordInstance, Qualid(List(Ident(fieldName)))) =>
      createFieldSelection(recordInstance, fieldName)
    case Qualid(List(Ident(primitiveValue)))
        if qualidIsPrimitiveValueInScala(primitiveValue) =>
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
      throw new IllegalStateException(
        "The following Coq term is not supported: " + anythingElse.toCoqCode);
  }

  private def blockTermToTreeHuggerAstList(term: Term): List[Tree] =
    term match {
      case SimpleLetIn(Ident(id), binders, typeTerm, inputTerm, mainTerm) =>
        (
          typeTerm.fold(VAL(id))(t => VAL(id, coqTypeToTreeHuggerType(t))) :=
            binders.fold(termToTreeHuggerAst(inputTerm))(
              createAnonymousFunction(_, inputTerm))
        ) :: blockTermToTreeHuggerAstList(mainTerm)
      case LetConstructorArgsIn(names, _, inputTerm, mainTerm) =>
        // TODO(Joseph Bakouny): consider supporting inductives with one constructor that are not tuples
        (
          VAL(convertTuple(names, PatternUtils.convertNameToPatternVar)) :=
            termToTreeHuggerAst(inputTerm)
        ) :: blockTermToTreeHuggerAstList(mainTerm)
      case LetPatternIn(pattern, inputTerm, _, mainTerm) =>
        (
          VAL(PatternUtils.convertPattern(pattern)) :=
            termToTreeHuggerAst(inputTerm)
        ) :: blockTermToTreeHuggerAstList(mainTerm)
      case nonBlockGeneratingTerm =>
        List(termToTreeHuggerAst(nonBlockGeneratingTerm))
    }

  private def coqTypeToTreeHuggerType(typeTerm: Term): Type = typeTerm match {
    case UncurriedTermApplication(genericTypeTerm, arguments) =>
      createTypeWithGenericParams(
        coqTypeToTreeHuggerType(genericTypeTerm),
        arguments.map {
          case Argument(_, typeTerm) => coqTypeToTreeHuggerType(typeTerm)
        })
    case ExplicitQualidApplication(id, genericTypeParams) =>
      createTypeWithGenericParams(
        coqTypeToTreeHuggerType(id),
        genericTypeParams.map(coqTypeToTreeHuggerType))
    case Term_->(typeTerm1, typeTerm2) =>
      // TODO (Joseph Bakouny): Coq -> in lemmas can have a different significance, check how this can be supported if needed ?
      coqTypeToTreeHuggerType(typeTerm1).TYPE_=>(
        coqTypeToTreeHuggerType(typeTerm2))
    case SimpleProjection(recordInstance @ Qualid(List(Ident(_))),
                          Qualid(List(Ident(fieldName)))) =>
      TYPE_REF(createFieldSelection(recordInstance, fieldName))
    case Qualid(xs) =>
      TYPE_REF(xs.map { case Ident(name) => convertType(name) }.mkString("."))
    case BetweenParenthesis(term) =>
      coqTypeToTreeHuggerType(term)
    case tupleDef @ InfixOperator(_, "*", _) =>
      def allTupleTypesIn(t: Term): List[Type] = t match {
        case InfixOperator(t1, "*", t2) =>
          allTupleTypesIn(t1) ::: allTupleTypesIn(t2)
        case typeTerm => List(coqTypeToTreeHuggerType(typeTerm))
      }
      TYPE_TUPLE(allTupleTypesIn(tupleDef))
    case anythingElse =>
      throw new IllegalStateException(
        "The following Coq type is not supported: " + anythingElse.toCoqCode);
  }

  private def createApplication(functionTerm: Term,
                                arguments: List[Argument]): Tree = {
    val (typeArguments, valueArguments) = functionTerm match {
      case Qualid(List(Ident(constructorName)))
          if (
            constructorToRecordTypeFields.get(constructorName).isDefined
              && constructorToRecordTypeFields(constructorName).size == arguments.size
          ) =>
        val (typeArgumentsWithBool, valueArgumentsWithBool) =
          (arguments zip constructorToRecordTypeFields(constructorName))
            .partition { case (_, isTypeArgument) => isTypeArgument }
        (
          typeArgumentsWithBool.map { case (arg, _)  => arg },
          valueArgumentsWithBool.map { case (arg, _) => arg }
        )
      case _ =>
        (List[Argument](), arguments)
    }
    curryingStrategy.createApplication(
      convertFunctionTermToTreeHuggerAst(functionTerm, typeArguments),
      valueArguments.map(convertValueArgumentToTreeHuggerAst)
    )
  }

  private def convertFunctionTermToTreeHuggerAst(functionTerm: Term,
                                                 typeArguments: List[Argument] =
                                                   List[Argument]()) = {
    val basicFunctionTerm = termToTreeHuggerAst(functionTerm)
    if (typeArguments.isEmpty)
      basicFunctionTerm
    else
      basicFunctionTerm.APPLYTYPE(
        typeArguments.map(convertTypeArgumentToToTreeHuggerType))
  }

  private def convertTypeArgumentToToTreeHuggerType(arg: Argument): Type =
    arg match {
      case Argument(None, BetweenParenthesis(argValue)) =>
        coqTypeToTreeHuggerType(argValue) // remove parenthesis since they are not needed in Scala
      case Argument(None, argValue) => coqTypeToTreeHuggerType(argValue)
      case anythingElse =>
        throw new IllegalStateException(
          "This Coq type cannot be converted to Scala: " + anythingElse.toCoqCode)
    }

  private def convertValueArgumentToTreeHuggerAst(arg: Argument): Tree =
    arg match {
      /*
       * Note (Joseph Bakouny): The Coq syntax "(ident := term)" should not be converted to Scala named arguments
       * since Coq only allows the application of this syntax to implicit parameters.
       * It should also be noted that implicit paremeters are currently converted to generics in Scala.
       */
      case Argument(None, BetweenParenthesis(argValue)) =>
        termToTreeHuggerAst(argValue) // remove parenthesis since they are not needed in Scala
      case Argument(None, argValue) => termToTreeHuggerAst(argValue)
      case Argument(Some(Ident(argName)), argValue) =>
        REF(argName) := termToTreeHuggerAst(argValue)
    }

  private def createFieldSelection(recordInstance: Term, fieldName: String) = {
    termToTreeHuggerAst(recordInstance).DOT(fieldName)
  }

  private def convertToScalaInfixOperator(coqOp: String): String = coqOp match {
    case "<=?"            => "<="
    case "<?"             => "<"
    case "=?"             => "=="
    case anyOtherOperator => anyOtherOperator
  }

  private def toNat(inputValue: Int): Tree = inputValue match {
    case 0          => REF("Zero")
    case n if n > 0 => REF("S") APPLY toNat(n - 1)
    case n if n < 0 =>
      throw new IllegalStateException(
        "Only Coq natural numbers are currently supported, the following negative number is, therefore, illegal: " + n)
  }

  private def qualidIsPrimitiveValueInScala(inputValue: String): Boolean =
    inputValue match {
      case "True"  => true
      case "true"  => true
      case "False" => true
      case "false" => true
      case _       => false
    }

  private def convertQualitToPrimitiveValue(inputValue: String) =
    inputValue match {
      case "True"  => LIT(true)
      case "true"  => LIT(true)
      case "False" => LIT(false)
      case "false" => LIT(false)
      // The code should never get here!
      case anythingElse =>
        throw new IllegalStateException(
          "This qualid is not a primitive value in Scala: " + anythingElse)
    }

  private def convertValue(inputValue: String): String = inputValue match {
    case "cons" => "Cons"
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
    case "string"       => "String"
    case "bool"         => "Boolean"
    case anyOtherString => anyOtherString
  }

  private def createAnonymousFunction(binders: Binders, bodyTerm: Term) = {
    def convertNamesToAnonFunParams(names: List[Name],
                                    optionalTypeTerm: Option[Term]) =
      names.map(
        name =>
          mkTreeFromDefStart(
            name match {
              case Name(Some(Ident(nameString))) =>
                optionalTypeTerm.fold {
                  PARAM(nameString)
                } { typeTerm: Term =>
                  PARAM(nameString, coqTypeToTreeHuggerType(typeTerm))
                }
              case Name(None) => PARAM(WILDCARD)
            }
        ))

    val Binders(bindersList) = binders
    val params = bindersList.flatMap {
      case ExplicitSimpleBinder(name) =>
        convertNamesToAnonFunParams(List(name), None)
      case ExplicitBinderWithType(names, typeTerm) =>
        convertNamesToAnonFunParams(names, Some(typeTerm))
      case ImplicitBinder(_, _) =>
        throw new IllegalStateException(
          "The implicit parameters of this anonymous function cannot be converted to Scala: " +
            Fun(binders, bodyTerm).toCoqCode)
    }

    curryingStrategy.createAnonymousFunction(params,
                                             termToTreeHuggerAst(bodyTerm))
  }

  private def createTypeAliasDefinition(id: Ident, binders: Option[Binders]) = {
    val typeParams = convertTypeBindersToTypeVars(binders)
    val Ident(nameString) = id
    TYPEVAR(nameString).withTypeParams(typeParams)
  }

  private def createDefinition(id: Ident,
                               binders: Option[Binders],
                               typeTerm: Option[Term]): DefTreeStart = {
    val Ident(definitionName) = id
    val declaration = createParameterlessDefinition(definitionName, typeTerm)

    binders.fold(declaration) { binders =>
      val (typeDefs, paramDefs) = partitionParams(binders)

      curryingStrategy.createDefinition(
        declaration.withTypeParams(typeDefs),
        paramDefs
      )
    }
  }

  private def createParameterlessDefinition(
      definitionName: String,
      typeTerm: Option[Term]): DefTreeStart =
    typeTerm.fold(
      DEFINFER(definitionName)
    )(
      typeTerm => DEF(definitionName, coqTypeToTreeHuggerType(typeTerm))
    )

  private def createCaseClassHierarchy(
      parentBinders: Option[Binders],
      parentName: String,
      indBodyItems: List[InductiveBodyItem]) = {
    val covariantParentTypeDefs =
      convertTypeBindersToTypeVars(parentBinders, covariant = true)

    val parentDeclaration: Tree =
      CLASSDEF(parentName)
        .withTypeParams(covariantParentTypeDefs)
        .withFlags(Flags.SEALED)
        .withFlags(Flags.ABSTRACT)
        .tree

    val caseClassHierarchy: List[Tree] =
      indBodyItems flatMap {
        /*
         * TODO (Jospeh Bakouny): This case clause ignores the type term.
         * Check what needs to be done with the type Term in future version
         */
        case InductiveBodyItem(Ident(name), binders, indBodyItemType) =>
          require(indBodyItemType.isEmpty,
                  "Return types of inductive body items should be ommitted")
          binders.fold {
            /*
             *   TODO(Joseph Bakouny): Fix the empty case class issue:
             *   An empty case class is not generated with the correct parenthesis "()".
             *
             *   This is probably an issue with treehugger.scala.
             */
            val caseObjectDeclaration: Tree =
              CASEOBJECTDEF(name)
                .withParents(
                  createTypeWithGenericParams(parentName,
                                              covariantParentTypeDefs.map(_ =>
                                                TYPE_REF("Nothing"))))
                .tree

            List(caseObjectDeclaration)
          } { binders =>
            val (typeDefs, paramsDefs) = partitionParams(binders)

            val parentTypeDefs = convertTypeBindersToTypeVars(parentBinders)
            val caseClassDeclaration: Tree =
              CASECLASSDEF(name)
                .withTypeParams(parentTypeDefs ::: typeDefs)
                .withParams(paramsDefs)
                .withParents(
                  createTypeWithGenericParams(parentName,
                                              parentTypeDefs.map(typeVar =>
                                                TYPE_REF(typeVar.name))))
                .tree

            val optionalCompanion =
              curryingStrategy.createCompanionObject(
                name,
                parentTypeDefs ::: typeDefs,
                paramsDefs)

            caseClassDeclaration ::
              optionalCompanion.fold[List[Tree]](Nil)(o => List(o))
          }
      }

    parentDeclaration :: caseClassHierarchy
  }

  private def partitionParams(
      binders: Binders): (List[TypeDefTreeStart], List[ValDef]) = {
    val Binders(bindersList) = binders

    val (typeParams, params) = bindersList.partition {
      /*
       *  TODO (Jospeh Bakouny): The partitioning algorithm between typeParams and params can be improved.
       *  In fact, in future versions, it might not be necessary to consider all implicit parameters as type params.
       *  Consider supporting converting implicit non-type params to Scala implicits.
       */
      case ImplicitBinder(_, Some(Set | Type)) => true
      case ImplicitBinder(_, None)             => true
      case ExplicitBinderWithType(_, _)        => false
      case anythingElse =>
        throw new IllegalStateException(
          "The following parameter notation is not supported: " + anythingElse.toCoqCode);
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

  private def convertTypeBindersToTypeVars(typeBinders: Option[Binders],
                                           covariant: Boolean = false) =
    typeBinders.fold(List[TypeDefTreeStart]()) {
      case Binders(binders) =>
        def convertNamesToTypeVars(names: List[Name]) = {
          for {
            Name(Some(Ident(nameString))) <- names
          } yield
            if (covariant)
              TYPEVAR(COVARIANT(nameString))
            else
              TYPEVAR(nameString)
        }
        binders.flatMap {
          case ExplicitSimpleBinder(name) => convertNamesToTypeVars(List(name))
          case ExplicitBinderWithType(names, Set | Type) =>
            convertNamesToTypeVars(names)
          case ImplicitBinder(names, None) => convertNamesToTypeVars(names)
          case ImplicitBinder(names, Some(Set | Type)) =>
            convertNamesToTypeVars(names)
          case anythingElse =>
            throw new IllegalStateException(
              "The following Coq type parameter is not supported: " + anythingElse)
        }
    }

  private def createTypeWithGenericParams(
      typeName: Type,
      genericTypeParams: List[Type]): Type = {
    typeName.TYPE_OF(genericTypeParams)
  }

  private def createInfixOperator(leftOp: Term, op: String, rightOp: Term) = {
    termToTreeHuggerAst(leftOp).INFIX(op).APPLY(termToTreeHuggerAst(rightOp))
  }

  private def convertTuple[A, B <: Tree](tupleElems: List[A],
                                         converterFunction: A => B): Tree = {
    tupleElems match {
      case Nil =>
        throw new IllegalStateException(
          "Cannot convert a tuple with no elements!")
      case p :: Nil =>
        converterFunction(p) // A tuple with a single element is just a value
      case _ :: _ => TUPLE(tupleElems.map(converterFunction))
    }
  }

  def convertNameToIdent(name: Name): Ident = name match {
    case Name(Some(id)) => id
    case Name(None) =>
      throw new IllegalStateException("This name is empty, it is a wildcard.")
  }

  def convertNameToString(name: Name): String = {
    val Ident(nameString) = convertNameToIdent(name)
    nameString
  }

  private object PatternUtils {

    def convertPatternMatch(patternMatch: Match): forest.Match = {
      // TODO(Joseph Bakouny): Check if the return type of the match should always be ignored
      val Match(matchItems, _, equations) = patternMatch
      convertTuple(matchItems, convertMatchItem).MATCH(
        equations.map(convertPatternEquation))
    }

    def convertPattern(coqPattern: Pattern): Tree = coqPattern match {
      /*
       * TODO (Joseph Bakouny):
       * Infix patterns are currently only used for the list cons operator
       * Check if there is another usage that should be implemented.
       */
      case InfixPattern(head, "::", tail) =>
        convertPattern(head) UNLIST_:: convertPattern(tail)
      case ConstructorPattern(constructor, args) =>
        termToTreeHuggerAst(constructor).UNAPPLY(args.map(convertPattern))
      case QualidPattern(q)  => termToTreeHuggerAst(q)
      case UnderscorePattern => WILDCARD
      /*
       * TODO (Joseph Bakouny): Handle Nats in pattern position correctly
       * Generate numbers such as 3 and not S(S(S(Zero))))
       * For this, consider subclassing BigInt and implementing unapply.
       */
      case NumberPattern(Number(n)) => toNat(n)
      case ParenthesisOrPattern(orPatterns) =>
        convertTuple(orPatterns, convertOrPattern)
      case anythingElse =>
        throw new IllegalStateException(
          "The following Coq pattern is not yet supported: " + anythingElse.toCoqCode);
    }

    def convertNameToPatternVar(name: Name): forest.Ident =
      name match {
        case Name(None)            => WILDCARD
        case Name(Some(Ident(id))) => ID(id)
      }

    private def convertMatchItem(matchItem: MatchItem): Tree = matchItem match {
      case MatchItem(coqTerm, None, None) => termToTreeHuggerAst(coqTerm)
      case anythingElse =>
        throw new IllegalStateException(
          "The following Coq match item is not supported: " + anythingElse.toCoqCode)
    }

    private def convertPatternEquation(patternEquation: PatternEquation) = {
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

  object RecordUtils {

    def createTreeHuggerAstFromRecord(record: Record): List[Tree] = {
      val recordDef = convertRecord(record)
      val optionalConstructor = createRecordConstructionFunction(record)

      // Note: Scallina does not generate the record constructor if its name is not explicitly specified
      optionalConstructor.fold {
        List(recordDef)
      } {
        List(recordDef, _)
      }
    }

    def convertRecordInstance(
        instanceName: String,
        args: Option[Binders],
        recordType: String,
        concreteRecordFields: List[ConcreteRecordField]): Tree = {

      val abstractFields = fetchRecordAbstractFields(recordType)

      val recordBlock = BLOCK(
        concreteRecordFields
          .map {
            case ConcreteRecordField(name, implementedBinders, _, bodyTerm) =>
              val AbstractRecordField(_, definedBinders, typeTerm) =
                abstractFields(convertNameToString(name))

              val potentialException =
                new IllegalStateException(
                  "The method signatures of instance " + instanceName + " should conform to signatures defined in record " + recordType + ":\n" +
                    implementedBinders.fold("()")(_.toCoqCode) + "\n" +
                    "Differ from:\n" +
                    definedBinders.fold("()")(_.toCoqCode))

              ConcreteRecordField(name,
                                  annotateParamsWithType(definedBinders,
                                                         implementedBinders,
                                                         potentialException),
                                  Some(typeTerm),
                                  bodyTerm)
          }
          .map(convertConcreteRecordField)
      )

      args.fold[Tree](
        OBJECTDEF(instanceName)
          .withParents(List(TYPE_REF(recordType))) := recordBlock
      ) { binders =>
        createDefinition(Ident(instanceName),
                         Some(binders),
                         Some(Qualid(List(Ident(recordType))))) :=
          NEW(
            ANONDEF(recordType) :=
              recordBlock
          )
      }

    }

    private def annotateParamsWithType(
        definedBinders: Option[Binders],
        implementedBinders: Option[Binders],
        potentialException: Exception): Option[Binders] = {
      (definedBinders, implementedBinders) match {
        case (None, None)             => None
        case (None, Some(Binders(_))) => throw potentialException
        case (Some(Binders(_)), None) => throw potentialException
        case (Some(Binders(defBinders)), Some(Binders(implBinders))) =>
          def expandExplicitBinders(binders: List[Binder]) = binders.flatMap {
            case ExplicitBinderWithType(names, typeTerm) =>
              names.map(name => ExplicitBinderWithType(List(name), typeTerm))
            case anthingElse => List(anthingElse)
          }

          val expandedDefBinders = expandExplicitBinders(defBinders)
          val expandedImplBinders = expandExplicitBinders(implBinders)

          if (expandedDefBinders.length != expandedImplBinders.length)
            throw potentialException

          Some(Binders(expandedDefBinders.zip(expandedImplBinders).map {
            case (ExplicitBinderWithType(List(_), typeTerm),
                  ExplicitSimpleBinder(implName)) =>
              ExplicitBinderWithType(List(implName), typeTerm)
            case (ExplicitBinderWithType(List(_), _),
                  implBinder @ ExplicitBinderWithType(List(_), _)) =>
              implBinder
            case (defBinder, implBinder) =>
              throw new IllegalStateException(
                "Unexpected record definition parameter: " + defBinder.toCoqCode + "\n" +
                  "And corresponding record instance parameter: " + implBinder.toCoqCode
              )
          }))
      }
    }

    private def fetchRecordAbstractFields(
        recordType: String): Map[String, AbstractRecordField] =
      (
        for {
          Record(_, Ident(recordName), None, None | Some(Type), _, fields) <- coqTrees
          if recordName == recordType
          abstractField @ AbstractRecordField(fieldName, _, _) <- fields
        } yield convertNameToString(fieldName) -> abstractField
      ).toMap

    private def convertRecord(record: Record): Tree = {
      val Record(_, Ident(recordName), binders, None | Some(Type), _, fields) =
        record

      TRAITDEF(recordName).withTypeParams(convertTypeBindersToTypeVars(binders)) :=
        BLOCK(
          fields.map(convertRecordField)
        )
    }

    private def createRecordConstructionFunction(
        record: Record): Option[Tree] = {

      val constructor = computeRecordConstructorName(record)

      constructor.map { constructorName =>
        val Record(_,
                   Ident(recordName),
                   binders,
                   None | Some(Type),
                   _,
                   fields) = record
        val abstractFields = filterAbstractRecordFields(fields)

        val typeBinderParams = convertTypeBindersToTypeVars(binders)

        val recordType = createTypeWithGenericParams(
          recordName,
          typeBinderParams.map(typeVar => TYPE_REF(typeVar.name)))
        val declaration = DEF(constructorName, recordType)

        val (typeFields, valueFields) =
          abstractFields.partition(recordFieldIsTypeField)
        val typeFieldParams = convertTypeFieldsToTypeVars(typeFields)
        val valueFieldParams = convertValueFieldsToParams(valueFields)

        val namePrefix = recordName + "_"
        curryingStrategy.createDefinition(
          declaration.withTypeParams(typeBinderParams ::: typeFieldParams),
          valueFieldParams
        ) := BLOCK(
          createFieldAliases(abstractFields, namePrefix) :+
            NEW(
              ANONDEF(recordType) :=
                BLOCK(assignFieldAliasesToNewRecordAbstractField(abstractFields,
                                                                 namePrefix))
            )
        )
      }
    }

    private def computeRecordConstructorName(record: Record): Option[String] = {
      val Record(_, Ident(_), _, None | Some(Type), constructor, _) = record
      constructor.map { case Ident(constructorName) => constructorName }
    }

    private def filterAbstractRecordFields(
        fields: List[RecordField]): List[AbstractRecordField] =
      for { abstractField @ AbstractRecordField(_, _, _) <- fields } yield
        abstractField

    private def extractNameFromRecordField(field: RecordField): String =
      field match {
        case AbstractRecordField(name, _, _)    => convertNameToString(name)
        case ConcreteRecordField(name, _, _, _) => convertNameToString(name)
      }

    private def assignFieldAliasesToNewRecordAbstractField(
        abstractFields: List[AbstractRecordField],
        namePrefix: String) =
      (abstractFields zip abstractFields.map(recordFieldIsTypeField)) map {
        case (typefield, true) =>
          convertAbstractRecordField(typefield) := TYPE_REF(
            namePrefix + extractNameFromRecordField(typefield))
        case (valuefield, false) =>
          convertAbstractRecordField(valuefield) := REF(
            namePrefix + extractNameFromRecordField(valuefield))
      }

    private def createFieldAliases(abstractFields: List[AbstractRecordField],
                                   namePrefix: String) =
      (abstractFields zip abstractFields.map(recordFieldIsTypeField)) map {
        case (typefield, true) => createTypeFieldAlias(typefield, namePrefix)
        case (valuefield, false) =>
          createValueFieldAlias(valuefield, namePrefix)
      }

    private def createTypeFieldAlias(typeField: RecordField,
                                     namePrefix: String) = {
      val name: String = extractNameFromRecordField(typeField)
      TYPEVAR(namePrefix + name) := TYPE_REF(name)
    }

    private def createValueFieldAlias(valueField: RecordField,
                                      namePrefix: String) = {
      val name: String = extractNameFromRecordField(valueField)
      DEF(namePrefix + name) := REF(name)
    }

    private def convertRecordField(recordField: RecordField): Tree =
      recordField match {
        case abstractRecordField @ AbstractRecordField(_, _, _) =>
          convertAbstractRecordField(abstractRecordField)
        case concreteRecordField @ ConcreteRecordField(_, _, _, _) =>
          convertConcreteRecordField(concreteRecordField)
      }

    private def convertAbstractRecordField(
        abstractRecordField: AbstractRecordField): Tree =
      (abstractRecordField, recordFieldIsTypeField(abstractRecordField)) match {
        case (AbstractRecordField(name, None, Type), true) =>
          createTypeAliasDefinition(convertNameToIdent(name), None)
        case (AbstractRecordField(name, binders, typeTerm), false) =>
          createRecordFieldDefinition(name, binders, typeTerm)
        case (anythingElse, _) =>
          throw new IllegalStateException(
            "This record field cannot be converted to Scala: " + anythingElse.toCoqCode)
      }

    private def convertConcreteRecordField(
        concreteRecordField: ConcreteRecordField): Tree =
      (concreteRecordField, recordFieldIsTypeField(concreteRecordField)) match {
        case (ConcreteRecordField(name, binders, Some(Type), bodyTypeTerm),
              true) =>
          createTypeAliasDefinition(convertNameToIdent(name), binders) :=
            coqTypeToTreeHuggerType(bodyTypeTerm)
        case (ConcreteRecordField(name, binders, Some(typeTerm), bodyTerm),
              false) =>
          createRecordFieldDefinition(name, binders, typeTerm) :=
            binders.fold(
              termToTreeHuggerAst(bodyTerm)
            )(
              createAnonymousFunction(_, bodyTerm)
            )
        case (anythingElse, _) =>
          throw new IllegalStateException(
            "This record field cannot be converted to Scala: " + anythingElse.toCoqCode)
      }

    private def createRecordFieldDefinition(name: Name,
                                            binders: Option[Binders],
                                            typeTerm: Term): Tree = {
      DEF(convertNameToString(name),
          computeFunctionReturnType(binders, typeTerm))
    }

    private def convertTypeFieldsToTypeVars(fields: List[AbstractRecordField]) =
      fields.map(field => TYPEVAR(extractNameFromRecordField(field)))

    private def convertValueFieldsToParams(fields: List[AbstractRecordField]) =
      for {
        AbstractRecordField(name, binders, typeTerm) <- fields
      } yield
        mkTreeFromDefStart(
          PARAM(convertNameToString(name),
                computeFunctionReturnType(binders, typeTerm)))

    private def computeFunctionReturnType(binders: Option[Binders],
                                          typeTerm: Term): Type =
      binders match {
        case Some(params) =>
          convertBindersToFunctionReturnType(params) TYPE_=> coqTypeToTreeHuggerType(
            typeTerm)
        case None => coqTypeToTreeHuggerType(typeTerm)
      }

    private def convertBindersToFunctionReturnType(binders: Binders): Type = {
      val Binders(params) = binders
      params
        .map {
          case ExplicitBinderWithType(names, typeTerm) =>
            val scalaType = coqTypeToTreeHuggerType(typeTerm)
            names.map(_ => scalaType).reduceRight(_ TYPE_=> _)
          case param @ (ExplicitSimpleBinder(_) | ImplicitBinder(_, _)) =>
            throw new IllegalStateException(
              "Illehgal abstract record field parameter: " + param.toCoqCode)
        }
        .reduceRight(_ TYPE_=> _)
    }
  }
}
