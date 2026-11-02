package scala.of.coq.parsercombinators.compiler

import customtreehugger.MyForest._
import definitions._
import treehuggerDSL._

import scala.of.coq.parsercombinators.parser.Argument
import scala.of.coq.parsercombinators.parser.BetweenParenthesis
import scala.of.coq.parsercombinators.parser.Binders
import scala.of.coq.parsercombinators.parser.BindNotationCommand
import scala.of.coq.parsercombinators.parser.BindNotationUse
import scala.of.coq.parsercombinators.parser.ListLiteral
import scala.of.coq.parsercombinators.parser.ListPattern
import scala.of.coq.parsercombinators.parser.CoqAST
import scala.of.coq.parsercombinators.parser.Definition
import scala.of.coq.parsercombinators.parser.FixBody
import scala.of.coq.parsercombinators.parser.Fixpoint
import scala.of.coq.parsercombinators.parser.Ident
import scala.of.coq.parsercombinators.parser.Inductive
import scala.of.coq.parsercombinators.parser.MutualInductive
import scala.of.coq.parsercombinators.parser.PrintAssumptions
import scala.of.coq.parsercombinators.parser.Prop
import scala.of.coq.parsercombinators.parser.ForAll
import scala.of.coq.parsercombinators.parser.InductiveBody
import scala.of.coq.parsercombinators.parser.InductiveBodyItem
import scala.of.coq.parsercombinators.parser.InfixOperator
import scala.of.coq.parsercombinators.parser.UnaryMinus
import scala.of.coq.parsercombinators.parser.MatchItem
import scala.of.coq.parsercombinators.parser.Name
import scala.of.coq.parsercombinators.parser.Number
import scala.of.coq.parsercombinators.parser.Qualid
import scala.of.coq.parsercombinators.parser.Term
import scala.of.coq.parsercombinators.parser.Term_->
import scala.of.coq.parsercombinators.parser.Term_%
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
import scala.of.coq.parsercombinators.parser.RequireImports
import scala.of.coq.parsercombinators.parser.ModuleImport
import scala.of.coq.parsercombinators.parser.InfixPattern
import scala.of.coq.parsercombinators.parser.ArgumentsCommand
import scala.of.coq.parsercombinators.parser.Type
import scala.of.coq.parsercombinators.parser.TupleValue
import scala.of.coq.parsercombinators.parser.ScopeCommand
import scala.of.coq.parsercombinators.parser.Fun
import scala.of.coq.parsercombinators.parser.LetConstructorArgsIn
import scala.of.coq.parsercombinators.parser.LetPatternIn
import scala.of.coq.parsercombinators.parser.SimpleLetIn
import scala.of.coq.parsercombinators.parser.Record
import scala.of.coq.parsercombinators.parser.RecordField
import scala.of.coq.parsercombinators.parser.RecordField
import scala.of.coq.parsercombinators.parser.AbstractRecordField
import scala.of.coq.parsercombinators.parser.ConcreteRecordField
import scala.of.coq.parsercombinators.parser.SimpleProjection

import RecordPreprocessor._
import scala.of.coq.parsercombinators.parser.RecordInstantiation
import scala.of.coq.parsercombinators.parser.Binder
import scala.of.coq.parsercombinators.parser.LoadCommand
import scala.of.coq.parsercombinators.parser.FunctionBody
import scala.of.coq.parsercombinators.parser.FunctionDef

import scala.of.coq.parsercombinators.parser.Set
import scala.of.coq.parsercombinators.parser.SetCommand

// TODO(Joseph Bakouny) restrict generics using Set instead of Type
class ScalaOfCoq(coqTrees: List[Sentence], curryingStrategy: CurryingStrategy, exactNumerics: Boolean = false,
                 nativeFullConstructors: Boolean = false, omitPeanoImport: Boolean = false,
                 recordContext: List[Record] = Nil, inductiveContext: List[Inductive] = Nil) {
  require(!nativeFullConstructors || curryingStrategy == Currify,
    "Native full constructors require curried functions")
  require(!omitPeanoImport || exactNumerics, "Peano import omission requires exact numerics")

  def createObjectFileCode(objectName: String): String = {
    "import scala.of.coq.lang._\n" +
      (if (exactNumerics && importsStdlibDecimal) "import scala.of.coq.exact.Decimal\n" else "") +
      (if (omitPeanoImport) "" else "import Nat._\n") +
      "import Pairs._\n" +
      "import Bools._\n" +
      "import MoreLists._\n" +
      "import scala.concurrent.Future\n" +
      "import MoreFutures._\n" +
      createObjectFileCodeWithoutDependantClasses(objectName)
  }

  def createObjectFileCodeWithoutDependantClasses(objectName: String): String = {
    treeToString(OBJECTDEF(objectName) := BLOCK(toTreeHuggerAst(coqTrees)))
  }

  def generateScalaCode: String = toTreeHuggerAst(coqTrees).map(treeToString(_)).mkString("\n")

  private val constructorToRecordTypeFields = computeConstructorToRecordTypeFields(recordContext ++ coqTrees)
  private val localConstructorNames = (inductiveContext ++ coqTrees).collect {
    case Inductive(InductiveBody(_, _, _, items)) => items.map(_.id.name)
  }.flatMap(names => names).toSet
  private val localTypeNames = coqTrees.collect {
    case Inductive(InductiveBody(Ident(name), _, _, _)) => name
    case Record(_, Ident(name), _, _, _, _) => name
  }.toSet
  private val caseInsensitiveTypeRenames: Map[String, String] = {
    val inductiveNames = coqTrees.collect {
      case Inductive(InductiveBody(Ident(name), _, _, _)) => name
    }
    def folded(name: String): String = name.toLowerCase(java.util.Locale.ROOT)
    val occupied = scala.collection.mutable.Set.empty[String] ++
      (localTypeNames ++ localConstructorNames).map(folded)
    inductiveNames.sorted.filter(name => localConstructorNames.exists(c => folded(c) == folded(name))).map { name =>
      val base = name + "_type"
      val renamed = Iterator.from(0).map(i => if (i == 0) base else base + i)
        .find(candidate => !occupied.contains(folded(candidate))).get
      occupied += folded(renamed)
      name -> renamed
    }.toMap
  }
  private def constructorArities(declarations: List[Sentence]): Map[String, Int] = declarations.collect {
    case Inductive(InductiveBody(_, _, _, items)) => items.map { item =>
      val count = item.binders match {
        case Some(Binders(binders)) => binders.map {
          case ExplicitSimpleBinder(_) => 1
          case ExplicitBinderWithType(names, _) => names.size
          case ImplicitBinder(_, _) => 0
        }.sum
        case None =>
          def arrowCount(term: Term): Int = term match {
            case Term_->(_, result) => 1 + arrowCount(result)
            case _ => 0
          }
          item.typeTerm.fold(0)(arrowCount)
      }
      item.id.name -> count
    }
  }.flatten.toMap
  private val localConstructorValueArity = constructorArities(inductiveContext ++ coqTrees)
  private val contextProjectionNames = recordContext.flatMap(_.fields.collect {
    case AbstractRecordField(Name(Some(Ident(name))), None, _) => name
    case ConcreteRecordField(Name(Some(Ident(name))), None, _, _) => name
  })
  require(contextProjectionNames.distinct.size == contextProjectionNames.size,
    "Ambiguous imported record projections require qualified context")
  private val contextConstructorNames = recordContext.flatMap(_.constructor.map(_.name)) ++
    inductiveContext.flatMap(_.indBody.indBodyItems.map(_.id.name))
  require(contextConstructorNames.distinct.size == contextConstructorNames.size,
    "Ambiguous imported record constructors require qualified context")
  private val localRecordProjectionNames = (coqTrees.collect {
    case Record(_, _, _, _, _, fields) => fields.collect {
      case AbstractRecordField(Name(Some(Ident(name))), None, _) => name
      case ConcreteRecordField(Name(Some(Ident(name))), None, _, _) => name
    }
  }.flatMap(names => names) ++ contextProjectionNames).toSet
  private val locallyDefinedNames = coqTrees.collect {
    case Definition(Ident(name), _, _, _) => name
    case Fixpoint(FixBody(Ident(name), _, _, _, _)) => name
    case FunctionDef(FunctionBody(Ident(name), _, _, _, _)) => name
  }.toSet
  private var visibleConstructorNames = contextConstructorNames.toSet
  private var visibleRecordProjectionNames = contextProjectionNames.toSet
  private var visibleConstructorValueArity = constructorArities(inductiveContext)
  private var visibleRecordConstructorFields = computeConstructorToRecordTypeFields(recordContext)
  private var visibleValueNames = scala.collection.immutable.Set.empty[String]
  private var lexicalValueNames = scala.collection.immutable.Set.empty[String]
  private var lexicalValueAliases = Map.empty[String, String]
  private def withValueBindings[A](bindings: Map[String, String])(body: => A): A = {
    val previousNames = lexicalValueNames
    val previousAliases = lexicalValueAliases
    lexicalValueNames = previousNames ++ bindings.keySet
    lexicalValueAliases = previousAliases ++ bindings
    try body finally {
      lexicalValueNames = previousNames
      lexicalValueAliases = previousAliases
    }
  }
  private def withValueNames[A](names: Iterable[String])(body: => A): A =
    withValueBindings(names.map(name => name -> unaliasedScalaIdentifier(name)).toMap)(body)
  private def withPatternNames[A](names: Iterable[String])(body: => A): A =
    withValueBindings(names.map(name => name -> patternValueAliases.getOrElse(name, unaliasedScalaIdentifier(name))).toMap)(body)
  private var generatedLetNames = scala.collection.immutable.Set.empty[String]
  private def freshLetName(name: String): String = {
    val stem = "scallinaLet_" + unaliasedScalaIdentifier(name)
    var candidate = stem
    var suffix = 0
    while (allSourceIdentifiers.contains(candidate) || generatedLetNames.contains(candidate) || lexicalValueAliases.values.exists(_ == candidate)) {
      suffix += 1
      candidate = stem + suffix
    }
    generatedLetNames += candidate
    candidate
  }
  private def withLetNames[A](names: Iterable[String])(body: => A): A =
    withValueBindings(names.map(name => name -> freshLetName(name)).toMap)(body)
  private def inConstructorPosition[A](body: => A): A = {
    val previousVisible = visibleValueNames
    val previousNames = lexicalValueNames
    val previousAliases = lexicalValueAliases
    visibleValueNames = scala.collection.immutable.Set.empty[String]
    lexicalValueNames = scala.collection.immutable.Set.empty[String]
    lexicalValueAliases = Map.empty[String, String]
    try body finally {
      visibleValueNames = previousVisible
      lexicalValueNames = previousNames
      lexicalValueAliases = previousAliases
    }
  }
  private def isValueBound(name: String): Boolean =
    visibleValueNames.contains(name) || lexicalValueNames.contains(name)
  private def namesInBinders(binders: Option[Binders]): List[String] = binders.toList.flatMap {
    case Binders(items) => items.flatMap {
      case ExplicitSimpleBinder(Name(Some(Ident(name)))) => List(name)
      case ExplicitSimpleBinder(_) => Nil
      case ExplicitBinderWithType(names, _) => names.collect { case Name(Some(Ident(name))) => name }
      case ImplicitBinder(names, _) => names.collect { case Name(Some(Ident(name))) => name }
    }
  }
  private def isStdlibImport(module: Qualid, fromPrefix: Option[Qualid], name: String): Boolean =
    module.idents.map(_.name) == List(name) &&
      fromPrefix.exists(prefix => List(List("Stdlib"), List("Coq")).contains(prefix.idents.map(_.name)))
  private def importsStdlib(name: String): Boolean = coqTrees.exists {
    case RequireImport(module, _, fromPrefix) => isStdlibImport(module, fromPrefix, name)
    case RequireImports(modules, _, fromPrefix) => modules.exists(isStdlibImport(_, fromPrefix, name))
    case _ => false
  }
  private val importsStdlibList = importsStdlib("List")
  private val importsStdlibPeanoNat = importsStdlib("PeanoNat")
  private val importsStdlibBool = importsStdlib("Bool")
  private val importsStdlibNArith = importsStdlib("NArith")
  private val importsStdlibZArith = importsStdlib("ZArith")
  private val importsStdlibDecimal = importsStdlib("Decimal")
  private var bindNotationAvailable = false
  private var listNotationAvailable = false
  private var activeNumericScopes: List[String] = Nil
  private var explicitNumericScope: Option[String] = None
  private var ignoredBinderCounter = 0
  private val exactPatternLiterals = scala.collection.mutable.LinkedHashMap.empty[BigInt, String]
  private def exactPatternLiteral(value: BigInt): Tree = {
    val name = exactPatternLiterals.getOrElseUpdate(value, {
      val stem = "ScallinaExactLiteral" + exactPatternLiterals.size
      var candidate = stem
      var suffix = 0
      while (sourceIdentifiers.contains(candidate) || exactPatternLiterals.values.exists(_ == candidate)) {
        suffix += 1
        candidate = stem + "_" + suffix
      }
      candidate
    })
    REF(name)
  }
  private lazy val sourceIdentifiers = coqTrees.map(_.toCoqCode).mkString("\n")
  private lazy val allSourceIdentifiers = sourceIdentifiers + "\n" +
    (recordContext ++ inductiveContext).map(_.toCoqCode).mkString("\n")
  private lazy val primedScalaNames: Map[String, String] = {
    val sourceNames = """[\p{L}_][\p{L}\p{N}_']*""".r.findAllIn(sourceIdentifiers).toSet
    var assigned = scala.collection.immutable.Set.empty[String]
    sourceNames.filter(_.contains("'")).toList.sorted.map { sourceName =>
      val stem = "scallinaPrime_" + sourceName.replace("'", "_prime")
      var candidate = stem
      var suffix = 0
      while (sourceIdentifiers.contains(candidate) || assigned.contains(candidate)) {
        suffix += 1
        candidate = stem + suffix
      }
      assigned += candidate
      sourceName -> candidate
    }.toMap
  }
  private lazy val patternValueAliases: Map[String, String] = {
    val allIdentifiers = sourceIdentifiers + "\n" + (recordContext ++ inductiveContext).map(_.toCoqCode).mkString("\n")
    val names = """[\p{L}_][\p{L}\p{N}_']*""".r.findAllIn(allIdentifiers).toSet
    var assigned = scala.collection.immutable.Set.empty[String]
    names.filter(name => name.length > 0 && Character.isUpperCase(name.charAt(0))).toList.sorted.map { name =>
      val stem = "scallinaPattern" + unaliasedScalaIdentifier(name)
      var candidate = stem
      var suffix = 0
      while (allIdentifiers.contains(candidate) || assigned.contains(candidate)) {
        suffix += 1
        candidate = stem + suffix
      }
      assigned += candidate
      name -> candidate
    }.toMap
  }
  private def nextIgnoredBinderName(): String = {
    ignoredBinderCounter += 1
    var candidate = "scallinaIgnoredArg" + ignoredBinderCounter
    while (sourceIdentifiers.contains(candidate)) {
      ignoredBinderCounter += 1
      candidate = "scallinaIgnoredArg" + ignoredBinderCounter
    }
    candidate
  }
  private def effectiveNumericScope: Option[String] = explicitNumericScope.orElse(activeNumericScopes.headOption)
  private def hasExplicitPropCodomain(term: Term): Boolean = term match {
    case Prop => true
    case Term_->(_, result) => hasExplicitPropCodomain(result)
    case ForAll(_, result) => hasExplicitPropCodomain(result)
    case BetweenParenthesis(inner) => hasExplicitPropCodomain(inner)
    case _ => false
  }
  private def withinNumericScope[A](scope: String)(body: => A): A = {
    val previous = explicitNumericScope
    explicitNumericScope = Some(scope)
    try body finally explicitNumericScope = previous
  }
  private val hasLocalListDefinition = coqTrees.exists {
    case Definition(Ident("list"), _, _, _) => true
    case Fixpoint(FixBody(Ident("list"), _, _, _, _)) => true
    case Inductive(InductiveBody(Ident("list"), _, _, _)) => true
    case _ => false
  }

  private def toTreeHuggerAst(coqTrees: List[Sentence]): List[Tree] = {
    bindNotationAvailable = false
    listNotationAvailable = false
    activeNumericScopes = Nil
    explicitNumericScope = None
    ignoredBinderCounter = 0
    exactPatternLiterals.clear()
    generatedLetNames = scala.collection.immutable.Set.empty[String]
    visibleConstructorNames = contextConstructorNames.toSet
    visibleRecordProjectionNames = contextProjectionNames.toSet
    visibleConstructorValueArity = constructorArities(inductiveContext)
    visibleRecordConstructorFields = computeConstructorToRecordTypeFields(recordContext)
    visibleValueNames = scala.collection.immutable.Set.empty[String]
    lexicalValueNames = scala.collection.immutable.Set.empty[String]
    lexicalValueAliases = Map.empty[String, String]
    val body = coqTrees.flatMap { sentence =>
      val result = toTreeHuggerAst(sentence)
      sentence match {
        case Definition(Ident(name), _, _, _) => visibleValueNames += name
        case Fixpoint(FixBody(Ident(name), _, _, _, _)) => visibleValueNames += name
        case FunctionDef(FunctionBody(Ident(name), _, _, _, _)) => visibleValueNames += name
        case inductive: Inductive =>
          val arities = constructorArities(List(inductive))
          visibleConstructorNames ++= arities.keySet
          visibleConstructorValueArity ++= arities
        case record: Record =>
          visibleConstructorNames ++= record.constructor.map(_.name)
          visibleRecordConstructorFields ++= computeConstructorToRecordTypeFields(List(record))
          visibleRecordProjectionNames ++= record.fields.collect {
            case AbstractRecordField(Name(Some(Ident(name))), None, _) => name
            case ConcreteRecordField(Name(Some(Ident(name))), None, _, _) => name
          }
        case _ => ()
      }
      result
    }
    val literals = exactPatternLiterals.toList.map { case (value, name) =>
      VAL(name).withFlags(Flags.PRIVATE) := REF("BigInt").APPLY(LIT(value.toString))
    }
    literals ++ body
  }

  private def toTreeHuggerAst(coqAst: Sentence): List[Tree] = coqAst match {
    case BindNotationCommand =>
      bindNotationAvailable = true
      List()
    case ModuleImport(moduleNames) =>
      if (moduleNames.exists(_.toCoqCode == "ListNotations")) listNotationAvailable = true
      List()
    case ScopeCommand(scopeName, _, operation) if exactNumerics =>
      val scope = scopeName.toCoqCode match {
        case "N_scope" => "N"
        case "nat_scope" => "nat"
        case "Z_scope" => "Z"
        case unsupported => throw new IllegalStateException("Exact numeric lowering does not support scope: " + unsupported)
      }
      if (operation == "Open") activeNumericScopes = scope :: activeNumericScopes.filterNot(_ == scope)
      else if (operation == "Close") activeNumericScopes = activeNumericScopes.filterNot(_ == scope)
      else throw new IllegalStateException("Unknown numeric scope operation: " + operation)
      List()
    case RequireImport(_, _, _) | RequireImports(_, _, _) | LoadCommand(_) | ArgumentsCommand(_, _) | ScopeCommand(_, _, _) | SetCommand(_) =>
      List() // The above commands do not generate any Scala code
    case PrintAssumptions(_) => List()
    case Definition(_, _, Some(Prop), _) => List()
    case Inductive(InductiveBody(_, _, Some(t), _)) if hasExplicitPropCodomain(t) => List()
    case MutualInductive(bodies) if bodies.forall(_.typeTerm.exists(hasExplicitPropCodomain)) => List()
    case MutualInductive(_) =>
      throw new IllegalStateException("Computational mutual inductives require a supported Scala lowering")
    case Definition(id, binders, Some(Set | Type), bodyTypeTerm) =>
      List(createTypeAliasDefinition(id, binders) := coqTypeToTreeHuggerType(bodyTypeTerm))
    case Definition(id, binders, None, bodyTypeTerm @ Term_%(_, Ident("type"))) =>
      List(createTypeAliasDefinition(id, binders) := coqTypeToTreeHuggerType(bodyTypeTerm))
    case Definition(id, binders, None, bodyTypeTerm @ UncurriedTermApplication(Qualid(List(Ident("list"))), List(Argument(None, _)))) if !hasLocalListDefinition =>
      List(createTypeAliasDefinition(id, binders) := coqTypeToTreeHuggerType(bodyTypeTerm))
    case Definition(Ident(name), args, Some(recordType), RecordInstantiation(concreteRecordFields)) =>
      withValueNames(namesInBinders(args)) {
        List(RecordUtils.convertRecordInstance(name, args, recordType, concreteRecordFields))
      }
    case Definition(id, binders, typeTerm, bodyTerm) =>
      withValueNames(namesInBinders(binders)) {
        List(createDefinition(id, binders, typeTerm) := termToTreeHuggerAst(bodyTerm))
      }
    case Inductive(InductiveBody(Ident(parentName), parentBinders, typeTerm, indBodyItems)) =>
      createCaseClassHierarchy(parentBinders, parentName, typeTerm, indBodyItems)
    case Fixpoint(FixBody(id, binders, _, typeTerm, bodyTerm)) =>
      withValueNames(id.name :: namesInBinders(Some(binders))) {
        List(createDefinition(id, Some(binders), typeTerm) := termToTreeHuggerAst(bodyTerm))
      }
    // NOTE(Joseph Bakouny): annotations should be ignored in Scala
    case FunctionDef(FunctionBody(id, binders, _, typeTerm, bodyTerm)) =>
      withValueNames(id.name :: namesInBinders(Some(binders))) {
        List(createDefinition(id, Some(binders), typeTerm) := termToTreeHuggerAst(bodyTerm))
      }
    case record @ Record(_, _, _, (None | Some(Set | Type)), _, _) =>
      RecordUtils.createTreeHuggerAstFromRecord(record)
    case Assertion(_, id, binders, bodyTerm) =>
      List()
    case anythingElse =>
      throw new IllegalStateException("The following Coq AST is not supported: " + anythingElse.toCoqCode);
  }

  private def termToScalaCode(t: Term): String = treeToString(termToTreeHuggerAst(t))

  private def arithmeticLevel(operator: String): Int = operator match {
    case "+" | "-" => 1
    case "*" | "/" | "mod" => 2
    case _ => 0
  }
  private def normalizeExactArithmetic(term: Term): Term = {
    def flatten(value: Term): (List[Term], List[String]) = value match {
      case InfixOperator(left, operator, right) if arithmeticLevel(operator) > 0 =>
        val (leftValues, leftOperators) = flatten(left)
        val (rightValues, rightOperators) = flatten(right)
        (leftValues ++ rightValues, leftOperators ++ List(operator) ++ rightOperators)
      case other => (List(other), Nil)
    }
    val (values, operators) = flatten(term)
    var operands = List(values.head)
    var pending = List.empty[String]
    def reduce(): Unit = {
      val right = operands.head
      val left = operands.tail.head
      operands = InfixOperator(left, pending.head, right) :: operands.drop(2)
      pending = pending.tail
    }
    operators.zip(values.tail).foreach { case (operator, value) =>
      while (pending.nonEmpty && arithmeticLevel(pending.head) >= arithmeticLevel(operator)) reduce()
      pending = operator :: pending
      operands = value :: operands
    }
    while (pending.nonEmpty) reduce()
    operands.head
  }

  private def termToTreeHuggerAst(t: Term): Tree = t match {
    case expression @ InfixOperator(_, operator, _) if exactNumerics && arithmeticLevel(operator) > 0 &&
        normalizeExactArithmetic(expression) != expression =>
      termToTreeHuggerAst(normalizeExactArithmetic(expression))
    case BindNotationUse(variable, received, body) =>
      if (!bindNotationAvailable)
        throw new IllegalStateException("Bind notation used before its exact declaration")
      termToTreeHuggerAst(UncurriedTermApplication(
        Qualid(List(Ident("bind"))),
        List(
          Argument(None, received),
          Argument(None, Fun(Binders(List(ExplicitSimpleBinder(variable))), body)))))
    case BetweenParenthesis(application: UncurriedTermApplication) =>
      termToTreeHuggerAst(application)
    case Fun(binders, bodyTerm) =>
      createAnonymousFunction(binders, bodyTerm)
    case letIn @ (SimpleLetIn(_, _, _, _, _) | LetConstructorArgsIn(_, _, _, _) | LetPatternIn(_, _, _, _)) =>
      BLOCK(blockTermToTreeHuggerAstList(letIn))
    case TermIf(conditionTerm, _, thenTerm, elseTerm) =>
      IF(termToTreeHuggerAst(conditionTerm)).THEN(termToTreeHuggerAst(thenTerm)).ELSE(termToTreeHuggerAst(elseTerm))
    case UncurriedTermApplication(Qualid(List(Ident("Nat"), Ident("div"))), List(Argument(None, numerator), Argument(None, denominator)))
        if exactNumerics =>
      createTotalNatDivision(numerator, denominator)
    case UncurriedTermApplication(Qualid(List(Ident("List"), Ident("rev"))), List(Argument(None, value)))
        if exactNumerics && importsStdlibList =>
      termToTreeHuggerAst(value).DOT("reverse")
    case UncurriedTermApplication(Qualid(List(Ident("Nat"), Ident("pred"))), List(Argument(None, value)))
        if exactNumerics && importsStdlibPeanoNat =>
      PAREN(termToTreeHuggerAst(value).INFIX("-").APPLY(REF("BigInt").APPLY(LIT("1"))))
        .DOT("max").APPLY(REF("BigInt").APPLY(LIT("0")))
    case UncurriedTermApplication(Qualid(List(Ident("N"), Ident(conversion @ ("of_nat" | "pos")))),
        List(Argument(None, value))) if exactNumerics && importsStdlibNArith =>
      REF("scala.of.coq.exact.ExactN." + (if (conversion == "of_nat") "ofNat" else "pos"))
        .APPLY(termToTreeHuggerAst(value))
    case UncurriedTermApplication(Qualid(List(Ident("N"), Ident("succ"))), List(Argument(None, value)))
        if exactNumerics && importsStdlibNArith =>
      PAREN(termToTreeHuggerAst(value).INFIX("+").APPLY(REF("BigInt").APPLY(LIT("1"))))
    case UncurriedTermApplication(Qualid(List(Ident("N"), Ident(operation @ ("eqb" | "ltb" | "leb")))),
        List(Argument(None, left), Argument(None, right))) if exactNumerics && importsStdlibNArith =>
      createInfixOperator(left, operation match {
        case "eqb" => "=="
        case "ltb" => "<"
        case "leb" => "<="
      }, right)
    case UncurriedTermApplication(Qualid(List(Ident("N"), Ident(conversion @ ("size" | "to_nat" | "to_uint")))),
        List(Argument(None, value))) if exactNumerics && importsStdlibNArith =>
      REF("scala.of.coq.exact.ExactN." + (conversion match {
        case "size" => "size"
        case "to_nat" => "toNat"
        case "to_uint" => "toUint"
      })).APPLY(termToTreeHuggerAst(value))
    case UncurriedTermApplication(Qualid(List(Ident("Z"), Ident("of_N"))),
        List(Argument(None, value))) if exactNumerics && importsStdlibZArith =>
      REF("scala.of.coq.exact.ExactZ.ofN").APPLY(termToTreeHuggerAst(value))
    case UncurriedTermApplication(Qualid(List(Ident("Z"), Ident(conversion @ ("of_nat" | "to_nat")))),
        List(Argument(None, value))) if exactNumerics && importsStdlibZArith =>
      REF("scala.of.coq.exact.ExactZ." + (if (conversion == "of_nat") "ofNat" else "toNat"))
        .APPLY(termToTreeHuggerAst(value))
    case UncurriedTermApplication(Qualid(List(Ident("Z"), Ident(operation @ ("leb" | "ltb")))),
        List(Argument(None, left), Argument(None, right))) if exactNumerics && importsStdlibZArith =>
      createInfixOperator(left, if (operation == "leb") "<=" else "<", right)
    case UncurriedTermApplication(Qualid(List(Ident("Nat"), Ident(operation @ ("ltb" | "leb" | "eqb")))),
        List(Argument(None, left), Argument(None, right)))
        if exactNumerics && importsStdlibPeanoNat =>
      createInfixOperator(left, operation match {
        case "ltb" => "<"
        case "leb" => "<="
        case "eqb" => "=="
      }, right)
    case UncurriedTermApplication(Qualid(List(Ident("Nat"), Ident("max"))),
        List(Argument(None, left), Argument(None, right)))
        if exactNumerics && importsStdlibPeanoNat =>
      termToTreeHuggerAst(left).DOT("max").APPLY(termToTreeHuggerAst(right))
    case UncurriedTermApplication(Qualid(List(Ident("length"))), List(Argument(None, values)))
        if exactNumerics && importsStdlibList && !isValueBound("length") =>
      REF("BigInt").APPLY(termToTreeHuggerAst(values).DOT("length"))
    case UncurriedTermApplication(Qualid(List(Ident(listPredicate @ ("forallb" | "existsb")))),
        List(Argument(None, predicate), Argument(None, values)))
        if exactNumerics && importsStdlibList && !isValueBound(listPredicate) =>
      termToTreeHuggerAst(values).DOT(if (listPredicate == "forallb") "forall" else "exists")
        .APPLY(termToTreeHuggerAst(predicate))
    case UncurriedTermApplication(Qualid(List(Ident("map"))),
        List(Argument(None, transform), Argument(None, values)))
        if exactNumerics && importsStdlibList && !isValueBound("map") =>
      termToTreeHuggerAst(values).DOT("map").APPLY(termToTreeHuggerAst(transform))
    case UncurriedTermApplication(Qualid(List(Ident("repeat"))),
        List(Argument(None, value), Argument(None, count)))
        if exactNumerics && importsStdlibList && !isValueBound("repeat") =>
      REF("scala.of.coq.exact.ExactList.repeat")
        .APPLY(termToTreeHuggerAst(value)).APPLY(termToTreeHuggerAst(count))
    case UncurriedTermApplication(Qualid(List(Ident(operation @ ("firstn" | "skipn")))),
        List(Argument(None, count), Argument(None, values)))
        if exactNumerics && importsStdlibList && !isValueBound(operation) =>
      REF("scala.of.coq.exact.ExactList." + operation)
        .APPLY(termToTreeHuggerAst(count)).APPLY(termToTreeHuggerAst(values))
    case UncurriedTermApplication(Qualid(List(Ident(fieldName))), List(Argument(None, recordValue)))
        if exactNumerics && visibleRecordProjectionNames.contains(fieldName) && !isValueBound(fieldName) =>
      termToTreeHuggerAst(recordValue).DOT(scalaIdentifier(fieldName))
    case UncurriedTermApplication(functionTerm, arguments) =>
      createApplication(functionTerm, arguments)
    case UnaryMinus(value) if exactNumerics && effectiveNumericScope.contains("Z") =>
      (REF("BigInt") APPLY LIT("0")).INFIX("-").APPLY(termToTreeHuggerAst(value))
    case UnaryMinus(_) if exactNumerics =>
      throw new IllegalStateException("Exact unary minus requires Z scope")
    case UnaryMinus(value) =>
      LIT(0).INFIX("-").APPLY(termToTreeHuggerAst(value))
    case InfixOperator(leftOp, op @ ("/" | "mod"), Number(divisor))
        if exactNumerics && effectiveNumericScope.contains("N") && divisor > 0 =>
      createInfixOperator(leftOp, op, Number(divisor))
    case InfixOperator(leftOp, "-", rightOp) if exactNumerics &&
        effectiveNumericScope.exists(scope => scope == "N" || scope == "nat") =>
      PAREN(createInfixOperator(leftOp, "-", rightOp)).DOT("max").APPLY(REF("BigInt") APPLY LIT("0"))
    case InfixOperator(leftOp, "-", rightOp) if exactNumerics && effectiveNumericScope.contains("Z") =>
      createInfixOperator(leftOp, "-", rightOp)
    case InfixOperator(_, op @ ("-" | "/" | "mod"), _) if exactNumerics =>
      throw new IllegalStateException("Exact numeric lowering is not defined for operator: " + op)
    case InfixOperator(_, op @ ("/\\" | "\\/" | "<->" | "<>"), _) =>
      throw new IllegalStateException("Propositional operator requires proof erasure before Scala lowering: " + op)
    case InfixOperator(leftOp, op, rightOp) => createInfixOperator(leftOp, convertToScalaInfixOperator(op), rightOp)
    case Term_%(term, Ident("bool")) if exactNumerics && importsStdlibBool =>
      termToTreeHuggerAst(term)
    case Term_%(term, Ident(scope @ ("N" | "nat" | "Z"))) if exactNumerics =>
      withinNumericScope(scope)(termToTreeHuggerAst(term))
    case Term_%(_, Ident(scope)) if exactNumerics =>
      throw new IllegalStateException("Exact numeric lowering does not support term scope: " + scope)
    // TODO(Joseph Bakouny): Check if the return type of the match should always be ignored
    case patternMatch @ Match(_, None, _) =>
      PatternUtils.convertPatternMatch(patternMatch)
    case SimpleProjection(recordInstance, Qualid(List(Ident(fieldName)))) =>
      createFieldSelection(recordInstance, fieldName)
    case Qualid(List(Ident("N"), Ident("to_nat"))) if exactNumerics && importsStdlibNArith =>
      REF("scala.of.coq.exact.ExactN.toNat")
    case Qualid(List(Ident(primitiveValue))) if !isValueBound(primitiveValue) && !visibleConstructorNames.contains(primitiveValue) && qualidIsPrimitiveValueInScala(primitiveValue) =>
      convertQualitToPrimitiveValue(primitiveValue)
    case Qualid(List(Ident("tt"))) if exactNumerics &&
        !visibleConstructorNames.contains("tt") && !isValueBound("tt") =>
      REF("()")
    case Qualid(List(Ident(zero @ "Z0"))) if exactNumerics && importsStdlibZArith &&
        !visibleConstructorNames.contains(zero) && !isValueBound(zero) =>
      REF("scala.of.coq.exact.ExactZ.Z0")
    case Qualid(List(Ident(signed @ ("Zpos" | "Zneg")))) if exactNumerics && importsStdlibZArith &&
        !visibleConstructorNames.contains(signed) && !isValueBound(signed) =>
      REF("scala.of.coq.exact.ExactZ." + signed)
    case Qualid(List(Ident(natural @ ("N0" | "Npos")))) if exactNumerics && importsStdlibNArith &&
        !visibleConstructorNames.contains(natural) && !isValueBound(natural) =>
      REF("scala.of.coq.exact.ExactN." + natural)
    case Qualid(List(Ident(binary @ ("xH" | "xO" | "xI")))) if exactNumerics && importsStdlibNArith &&
        !visibleConstructorNames.contains(binary) && !isValueBound(binary) =>
      REF("scala.of.coq.exact.ExactPositive." + binary)
    case Qualid(List(Ident(natConstructor @ ("O" | "S")))) if exactNumerics && !isValueBound(natConstructor) =>
      if (visibleConstructorNames.contains(natConstructor))
        throw new IllegalStateException("Exact natural constructor is shadowed locally: " + natConstructor)
      REF("scala.of.coq.exact.ExactNat." + natConstructor)
    case Qualid(List(Ident(name))) =>
      REF(convertValue(name))
    case Qualid(xs) =>
      REF(xs.map { case Ident(name) => unaliasedScalaIdentifier(name) }.mkString("."))
    case Number(n) if exactNumerics => REF("BigInt") APPLY LIT(n.toString)
    case Number(n) =>
      if (n.isValidInt) LIT(n.toInt)
      else REF("BigInt") APPLY LIT(n.toString)
    case ListLiteral(elements) =>
      if (!listNotationAvailable)
        throw new IllegalStateException("List notation used before importing ListNotations")
      if (elements.isEmpty) REF("Nil")
      else REF("List").APPLY(elements.map(termToTreeHuggerAst))
    case BetweenParenthesis(term) =>
      PAREN(termToTreeHuggerAst(term))
    case TupleValue(tupleTerms) =>
      convertTuple(tupleTerms, termToTreeHuggerAst)
    case anythingElse =>
      throw new IllegalStateException("The following Coq term is not supported: " + anythingElse.toCoqCode);
  }

  private def blockTermToTreeHuggerAstList(term: Term): List[Tree] = term match {
    case SimpleLetIn(Ident(id), binders, typeTerm, inputTerm, mainTerm) =>
      val input = binders.fold(termToTreeHuggerAst(inputTerm))(createAnonymousFunction(_, inputTerm))
      val annotation = typeTerm.map(coqTypeToTreeHuggerType)
      withLetNames(List(id)) {
        (annotation.fold(VAL(scalaIdentifier(id)))(t => VAL(scalaIdentifier(id), t)) := input) ::
          blockTermToTreeHuggerAstList(mainTerm)
      }
    case LetConstructorArgsIn(names, _, inputTerm, mainTerm) =>
      val boundNames = names.collect { case Name(Some(Ident(name))) => name }
      val input = termToTreeHuggerAst(inputTerm)
      withLetNames(boundNames) {
        (VAL(convertTuple(names, PatternUtils.convertNameToPatternVar)) := input) ::
          blockTermToTreeHuggerAstList(mainTerm)
      }
    case LetPatternIn(pattern, inputTerm, _, mainTerm) =>
      val input = termToTreeHuggerAst(inputTerm)
      withLetNames(PatternUtils.boundNames(pattern)) {
        (VAL(PatternUtils.convertPattern(pattern)) := input) :: blockTermToTreeHuggerAstList(mainTerm)
      }
    case nonBlockGeneratingTerm =>
      List(termToTreeHuggerAst(nonBlockGeneratingTerm))
  }

  private def coqTypeToScalaCode(typeTerm: Term): String = treeToString(coqTypeToTreeHuggerType(typeTerm))

  private def coqTypeToTreeHuggerType(typeTerm: Term): Type = typeTerm match {
    case Term_%(term, Ident("type")) =>
      coqTypeToTreeHuggerType(term)
    case UncurriedTermApplication(genericTypeTerm, arguments) =>
      createTypeWithGenericParams(coqTypeToTreeHuggerType(genericTypeTerm), arguments.map {
        case Argument(_, typeTerm) => coqTypeToTreeHuggerType(typeTerm)
      })
    case ExplicitQualidApplication(id, genericTypeParams) =>
      createTypeWithGenericParams(coqTypeToTreeHuggerType(id), genericTypeParams.map(coqTypeToTreeHuggerType(_)))
    case Term_->(typeTerm1, typeTerm2) =>
      def converseParensIfNeeded(typeTerm: Term): Type = typeTerm match {
        case BetweenParenthesis(t @ Term_->(_, _)) => TYPE_REF(PAREN(coqTypeToTreeHuggerType(t)))
        case otherType                             => coqTypeToTreeHuggerType(otherType)
      }
      converseParensIfNeeded(typeTerm1).TYPE_=>(converseParensIfNeeded(typeTerm2))
    case SimpleProjection(recordInstance @ Qualid(List(Ident(_))), Qualid(List(Ident(fieldName)))) =>
      TYPE_REF(createFieldSelection(recordInstance, fieldName))
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

  private def createApplication(functionTerm: Term, arguments: List[Argument]): Tree = {
    val (typeArguments, valueArguments) = functionTerm match {
      case Qualid(List(Ident(constructorName))) if (
        !isValueBound(constructorName) && visibleRecordConstructorFields.get(constructorName).isDefined
        && visibleRecordConstructorFields(constructorName).size == arguments.size) =>
        val (typeArgumentsWithBool, valueArgumentsWithBool) = (arguments zip visibleRecordConstructorFields(constructorName)).partition { case (arg, isTypeArgument) => isTypeArgument }
        (
          typeArgumentsWithBool.map { case (arg, b) => arg },
          valueArgumentsWithBool.map { case (arg, b) => arg })
      case _ =>
        (List[Argument](), arguments)
    }
    val convertedArguments = valueArguments.map(convertValueArgumentToTreeHuggerAst)
    functionTerm match {
      case Qualid(List(Ident(name))) if nativeFullConstructors &&
        visibleConstructorValueArity.contains(name) && !isValueBound(name) =>
        if (exactNumerics && (name == "O" || name == "S"))
          throw new IllegalStateException("Exact natural constructor is shadowed locally: " + name)
        if (typeArguments.nonEmpty)
          throw new IllegalStateException("Native constructor has unsupported explicit type arguments: " + name)
        val arity = visibleConstructorValueArity(name)
        if (arity != convertedArguments.size)
          throw new IllegalStateException("Local constructor requires all value arguments: " + name)
        NEW(name, convertedArguments: _*)
      case _ =>
        curryingStrategy.createApplication(
          convertFunctionTermToTreeHuggerAst(functionTerm, typeArguments),
          convertedArguments)
    }
  }

  private def createTotalNatDivision(numerator: Term, denominator: Term): Tree = {
    val numeratorName = "scallinaNatNumerator"
    val denominatorName = "scallinaNatDenominator"
    val zero = REF("BigInt") APPLY LIT("0")
    val body = IF(REF(denominatorName).INFIX("==").APPLY(zero))
      .THEN(zero)
      .ELSE(REF(numeratorName).INFIX("/").APPLY(REF(denominatorName)))
    val params = List(numeratorName, denominatorName).map(name =>
      mkTreeFromDefStart(PARAM(name, TYPE_REF("BigInt"))))
    val lambda = NoCurrying.createAnonymousFunction(params, body)
    PAREN(lambda).APPLY(List(termToTreeHuggerAst(numerator), termToTreeHuggerAst(denominator)))
  }

  private def convertFunctionTermToTreeHuggerAst(functionTerm: Term, typeArguments: List[Argument] = List[Argument]()) = {
    val basicFunctionTerm = termToTreeHuggerAst(functionTerm)
    if (typeArguments.isEmpty)
      basicFunctionTerm
    else
      basicFunctionTerm.APPLYTYPE(typeArguments.map(convertTypeArgumentToToTreeHuggerType))
  }

  private def convertTypeArgumentToToTreeHuggerType(arg: Argument): Type = arg match {
    case Argument(None, BetweenParenthesis(argValue)) => coqTypeToTreeHuggerType(argValue) // remove parenthesis since they are not needed in Scala
    case Argument(None, argValue)                     => coqTypeToTreeHuggerType(argValue)
    case anythingElse =>
      throw new IllegalStateException("This Coq type cannot be converted to Scala: " + anythingElse.toCoqCode)
  }

  private def convertValueArgumentToTreeHuggerAst(arg: Argument): Tree = arg match {
    /*
     * Note (Joseph Bakouny): The Coq syntax "(ident := term)" should not be converted to Scala named arguments
     * since Coq only allows the application of this syntax to implicit parameters.
     * It should also be noted that implicit paremeters are currently converted to generics in Scala.
     */
    case Argument(None, BetweenParenthesis(argValue)) => termToTreeHuggerAst(argValue) // remove parenthesis since they are not needed in Scala
    case Argument(None, argValue)                     => termToTreeHuggerAst(argValue)
    case Argument(Some(Ident(argName)), argValue)     => REF(scalaIdentifier(argName)) := termToTreeHuggerAst(argValue)
  }

  private def createFieldSelection(recordInstance: Term, fieldName: String) = {
    termToTreeHuggerAst(recordInstance).DOT(scalaIdentifier(fieldName))
  }

  private def convertToScalaInfixOperator(coqOp: String): String = coqOp match {
    case "<=?"            => "<="
    case "<?"             => "<"
    case "=?"             => "=="
    case anyOtherOperator => anyOtherOperator
  }

  private def toNat(inputValue: BigInt): Tree = {
    if (!inputValue.isValidInt)
      throw new IllegalStateException("Large numeric patterns require a target-specific extraction mapping: " + inputValue)
    inputValue.toInt match {
      case 0            => REF("Zero")
      case n if (n > 0) => REF("S") APPLY toNat(BigInt(n - 1))
      case n if (n < 0) => throw new IllegalStateException("Only Coq natural numbers are currently supported, the following negative number is, therefore, illegal: " + n)
    }
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

  private def convertValue(inputValue: String): String =
    if (isValueBound(inputValue)) scalaIdentifier(inputValue) else convertGlobalValue(inputValue)

  private def convertGlobalValue(inputValue: String): String = inputValue match {
    case "cons"         => "Cons"
    // TODO (Joseph Bakouny): Leon "Nil" lists are written like this "Nil()" in pattern matches, check how to support this
    case "nil"          => "Nil"
    case "pair"         => "Tuple2"
    case anyOtherString => unaliasedScalaIdentifier(anyOtherString)
  }

  private def scalaIdentifier(name: String): String =
    lexicalValueAliases.getOrElse(name, unaliasedScalaIdentifier(name))
  private def unaliasedScalaIdentifier(name: String): String =
    if (name.contains("'"))
      primedScalaNames.getOrElse(name,
        throw new IllegalStateException("Primed identifier missing from source: " + name))
    else name

  private def convertType(inputType: String): String = inputType match {
    case "unit" if exactNumerics && !localTypeNames.contains("unit") &&
      !locallyDefinedNames.contains("unit") => "Unit"
    case "positive" if exactNumerics && !localTypeNames.contains("positive") => "BigInt"
    case "N" | "nat" | "Z" if exactNumerics => "BigInt"
    case "Z"            => "BigInt"
    case "nat"          => "Nat"
    case "list"         => "List"
    case "option"       => "Option"
    case "string"       => "String"
    case "bool"         => "Boolean"
    case anyOtherString => caseInsensitiveTypeRenames.getOrElse(anyOtherString, anyOtherString)
  }

  private def createAnonymousFunction(binders: Binders, bodyTerm: Term) = withValueNames(namesInBinders(Some(binders))) {
    def convertNamesToAnonFunParams(names: List[Name], optionalTypeTerm: Option[Term]) =
      names.map(name =>
        mkTreeFromDefStart(
          name match {
            case Name(Some(Ident(nameString))) =>
              optionalTypeTerm.fold {
                PARAM(scalaIdentifier(nameString))
              } {
                (typeTerm: Term) =>
                  PARAM(scalaIdentifier(nameString), coqTypeToTreeHuggerType(typeTerm))
              }
            case Name(None) => PARAM(WILDCARD)
          }))

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
    TYPEVAR(scalaIdentifier(nameString)).withTypeParams(typeParams)
  }

  private def createDefinition(id: Ident, binders: Option[Binders], typeTerm: Option[Term]): DefTreeStart = {
    val Ident(definitionName) = id
    val declaration = createParameterlessDefinition(scalaIdentifier(definitionName), typeTerm)

    binders.fold(declaration) {
      binders =>
        val (typeDefs, paramDefs) = partitionParams(binders)

        curryingStrategy.createDefinition(
          declaration.withTypeParams(typeDefs),
          paramDefs)
    }
  }

  private def createParameterlessDefinition(definitionName: String, typeTerm: Option[Term]): DefTreeStart =
    typeTerm.fold(
      DEFINFER(definitionName))(
        typeTerm => DEF(definitionName, coqTypeToTreeHuggerType(typeTerm)))

  private def createCaseClassHierarchy(parentBinders: Option[Binders], parentName: String, typeTerm: Option[Term], indBodyItems: List[InductiveBodyItem]) = {

    val GADT_NumberOfParams = typeTerm.fold[Option[Int]](
      None // Not a GADT
    ) {
      case Set | Type => None // Not a GADT
      case arrowType @ Term_->(_, _) =>
        def calculateGADTnbParams(t: Term): Int = t match {
          case Set | Type                => 0 // stop recursion
          case Term_->(Set | Type, tail) => 1 + calculateGADTnbParams(tail)
          case anythingElse =>
            throw new IllegalStateException("Illegal GADT top-level return type: " + anythingElse.toCoqCode)
        }
        Some(calculateGADTnbParams(arrowType))
      case anythingElse =>
        throw new IllegalStateException("Illegal Inductive return type: " + anythingElse.toCoqCode)
    }

    // GADT cannot define top-level type params
    require(!(GADT_NumberOfParams.isDefined && parentBinders.isDefined), "GADTs are not allowed to have top-level parameters in Scallina!")

    val covariantParentTypeDefs = GADT_NumberOfParams.fold[List[TypeDefTreeStart]](
      convertTypeBindersToTypeVars(parentBinders, true) // Not a GADT
    ) {
        numberOfParams => // Generate GADT type parameters at the Scala trait-level
          (0 to numberOfParams - 1).toList.map(i => ('A' to 'Z')(i)).map(c => TYPEVAR(c.toString))
      }

    val parentDeclaration: Tree =
      CLASSDEF(caseInsensitiveTypeRenames.getOrElse(parentName, parentName))
        .withTypeParams(covariantParentTypeDefs)
        .withFlags(Flags.SEALED)
        .withFlags(Flags.ABSTRACT)
        .tree

    val caseClassHierarchy: List[Tree] =
      indBodyItems flatMap {
        case InductiveBodyItem(Ident(name), binders, indBodyItemType) =>
          def arrowArguments(term: Term): (List[Term], Term) = term match {
            case Term_->(argument, result) =>
              val (remaining, returnType) = arrowArguments(result)
              (argument :: remaining, returnType)
            case returnType => (Nil, returnType)
          }

          val (constructorBinders, constructorReturnType) = (binders, indBodyItemType) match {
            case (None, Some(arrow: Term_->)) =>
              val (arguments, returnType) = arrowArguments(arrow)
              val generatedBinders = arguments.zipWithIndex.map { case (argument, index) =>
                ExplicitBinderWithType(List(Name(Some(Ident("arg" + (index + 1))))), argument)
              }
              (Some(Binders(generatedBinders)), Some(returnType))
            case _ => (binders, indBodyItemType)
          }

          // If a simple return type was explicitely specified, use it!
          val returnTypeIndBodyItem = constructorReturnType.map {
            case genericApplication @ (UncurriedTermApplication(_, _) | ExplicitQualidApplication(_, _)) =>
              coqTypeToTreeHuggerType(genericApplication)
            case anythingElse =>
              throw new IllegalStateException("Unsupported inductive body return type:" + anythingElse.toCoqCode)
          }

          constructorBinders.fold {
            val caseObjectDeclaration: Tree =
              CASEOBJECTDEF(name)
                .withParents(
                  if (!parentBinders.isDefined && returnTypeIndBodyItem.isDefined) // case of GADTs
                    returnTypeIndBodyItem.get
                  // No binders + no parent binders => no type paremeters
                  //=> no need to insert Scala's Nothing
                  else //If parent binders are defined => This is not a GADT, see below
                    // Given the fact that we have no binders at the constructor-level
                    //-> ignore specific return type and add Nothing instead of generics
                    // Note that, to ensure correctness:
                    // Scallina prohibits GADTs from having parent binders (top-level parameters)
                    createTypeWithGenericParams(TYPE_REF(caseInsensitiveTypeRenames.getOrElse(parentName, parentName)), covariantParentTypeDefs.map(_ => TYPE_REF("Nothing"))))
                .tree

            List(caseObjectDeclaration)
          } {
            binders =>
              val (typeDefs, paramsDefs) = partitionParams(binders)

              val parentTypeDefs = convertTypeBindersToTypeVars(parentBinders)
              val caseClassDeclaration: Tree =
                CASECLASSDEF(name)
                  .withTypeParams(parentTypeDefs ::: typeDefs)
                  .withParams(paramsDefs)
                  .withParents(
                    returnTypeIndBodyItem.fold(
                      createTypeWithGenericParams(TYPE_REF(caseInsensitiveTypeRenames.getOrElse(parentName, parentName)), parentTypeDefs.map(typeVar => TYPE_REF(typeVar.name)))
                    // No return type was specified, generate it from the environment
                    )(
                        x => x // A return type was explicitly specified, keep it as it is => this could serve for GADTs
                      ))
                  .tree

              val optionalCompanion =
                if (nativeFullConstructors && curryingStrategy == Currify)
                  None
                else
                  curryingStrategy.createCompanionObject(name, parentTypeDefs ::: typeDefs, paramsDefs)

              caseClassDeclaration ::
                optionalCompanion.fold[List[Tree]](Nil)(o => List(o))
          }
      }

    parentDeclaration :: caseClassHierarchy
  }

  private def isTypeBinder(binder: Binder): Boolean = binder match {
    /*
       *  TODO (Jospeh Bakouny): The partitioning algorithm between typeParams and params can be improved.
       *  In fact, in future versions, it might not be necessary to consider all implicit parameters as type params.
       *  Consider supporting converting implicit non-type params to Scala implicits.
       */
    case ImplicitBinder(_, Some(Set | Type)) => true
    case ImplicitBinder(_, None)             => true
    case ExplicitBinderWithType(_, _)        => false
    case anythingElse =>
      throw new IllegalStateException("The following parameter notation is not supported: " + anythingElse.toCoqCode);
  }

  private def convertTypeBinders(typeBinders: List[Binder]): List[TypeDefTreeStart] =
    for {
      ImplicitBinder(names, _) <- typeBinders
      Name(Some(Ident(nameString))) <- names
    } yield TYPEVAR(nameString)

  private def convertValueBinders(valueBinders: List[Binder]): List[ValDef] =
    // TODO (Joseph Bakouny): Should we take currying into consideration ?
    for {
      ExplicitBinderWithType(names, typeTerm) <- valueBinders
      name <- names
    } yield {
      name match {
        case Name(Some(Ident(nameString))) =>
          mkTreeFromDefStart(PARAM(scalaIdentifier(nameString), coqTypeToTreeHuggerType(typeTerm)))
        case Name(None) =>
          mkTreeFromDefStart(PARAM(nextIgnoredBinderName(), coqTypeToTreeHuggerType(typeTerm)))
      }
    }

  private def partitionParams(binders: Binders): (List[TypeDefTreeStart], List[ValDef]) = {
    val Binders(bindersList) = binders;

    val (typeParams, params) = bindersList.partition(isTypeBinder)

    val implicitBinders: List[TypeDefTreeStart] = convertTypeBinders(typeParams)

    val paramsDefs: List[ValDef] = convertValueBinders(params)

    (implicitBinders, paramsDefs)
  }

  private def getNamesFromTypeParameter(binders: List[Binder]): List[Name] =
    binders.flatMap {
      case ExplicitSimpleBinder(name)                => List(name)
      case ExplicitBinderWithType(names, Set | Type) => names
      case ImplicitBinder(names, None)               => names
      case ImplicitBinder(names, Some(Set | Type))   => names
      case anythingElse =>
        throw new IllegalStateException("The following Coq type parameter is not supported: " + anythingElse)
    }

  private def convertTypeBindersToTypeVars(typeBinders: Option[Binders], covariant: Boolean = false): List[TypeDefTreeStart] =

    typeBinders.fold(List[TypeDefTreeStart]()) {
      case Binders(binders) =>
        def convertNamesToTypeVars(names: List[Name]) = {
          for {
            Name(Some(Ident(nameString))) <- names
          } yield (
            if (covariant)
              TYPEVAR(COVARIANT(nameString))
            else
              TYPEVAR(nameString))
        }
        convertNamesToTypeVars(getNamesFromTypeParameter(binders))
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

  def convertNameToIdent(name: Name): Ident = name match {
    case Name(Some(id)) => id
    case Name(None)     => throw new IllegalStateException("This name is empty, it is a wildcard.")
  }

  def convertNameToString(name: Name): String = {
    val Ident(nameString) = convertNameToIdent(name)
    nameString
  }

  private object PatternUtils {
    private val primitiveConstructors = scala.collection.immutable.Set(
      "O", "S", "true", "false", "nil", "cons", "pair", "None", "Some", "tt",
      "N0", "Npos", "Z0", "Zpos", "Zneg", "xH", "xO", "xI")
    def boundNames(pattern: Pattern): List[String] = pattern match {
      case QualidPattern(Qualid(List(Ident(name))))
          if !visibleConstructorNames.contains(name) && !contextConstructorNames.contains(name) &&
             !primitiveConstructors.contains(name) =>
        val upper = name.length > 0 && Character.isUpperCase(name.charAt(0))
        if (upper && name != "True" && name != "False") {
          if (exactNumerics)
            throw new IllegalStateException("Exact uppercase pattern requires constructor declaration context or checked binder normalization: " + name)
          Nil
        } else List(name)
      case ConstructorPattern(_, arguments) => arguments.flatMap(boundNames)
      case InfixPattern(left, _, right) => boundNames(left) ++ boundNames(right)
      case ListPattern(elements) => elements.flatMap(boundNames)
      case ParenthesisOrPattern(alternatives) => alternatives.flatMap {
        case OrPattern(patterns) => patterns.flatMap(boundNames)
      }
      case _ => Nil
    }


    def convertPatternMatch(patternMatch: Match) = {
      // TODO(Joseph Bakouny): Check if the return type of the match should always be ignored
      val Match(matchItems, _, equations) = patternMatch
      val cases = if (exactNumerics) equations.flatMap(convertPatternEquationExpanded)
      else equations.map(convertPatternEquation)
      convertTuple(matchItems, convertMatchItem).MATCH(cases)
    }

    def convertPattern(coqPattern: Pattern): Tree = coqPattern match {
      /*
     * TODO (Joseph Bakouny):
     * Infix patterns are currently only used for the list cons operator
     * Check if there is another usage that should be implemented.
     */
      case InfixPattern(head, "::", tail)        => convertPattern(head) UNLIST_:: (convertPattern(tail))
      case ConstructorPattern(constructor, args) => inConstructorPosition(termToTreeHuggerAst(constructor)).UNAPPLY(args.map(convertPattern))
      case variable @ QualidPattern(Qualid(List(Ident(name)))) if boundNames(variable).contains(name) =>
        ID(scalaIdentifier(name))
      case QualidPattern(q) => inConstructorPosition(termToTreeHuggerAst(q))
      case ListPattern(elements) =>
        if (!listNotationAvailable)
          throw new IllegalStateException("List pattern used before importing ListNotations")
        elements.foldRight(REF("Nil"): Tree)((element, tail) => convertPattern(element) UNLIST_:: tail)
      case UnderscorePattern                     => WILDCARD
      /*
       * TODO (Joseph Bakouny): Handle Nats in pattern position correctly
       * Generate numbers such as 3 and not S(S(S(Zero))))
       * For this, consider subclassing BigInt and implementing unapply.
       */
      case NumberPattern(Number(n))              => if (exactNumerics) exactPatternLiteral(n) else toNat(n)
      case ParenthesisOrPattern(orPatterns)      => convertTuple(orPatterns, convertOrPattern)
      case anythingElse =>
        throw new IllegalStateException("The following Coq pattern is not yet supported: " + anythingElse.toCoqCode);
    }

    def convertNameToPatternVar(name: Name) =
      name match {
        case Name(None)            => WILDCARD
        case Name(Some(Ident(id))) => ID(scalaIdentifier(id))
      }

    private def convertMatchItem(matchItem: MatchItem): Tree = matchItem match {
      case MatchItem(coqTerm, None, None) => termToTreeHuggerAst(coqTerm)
      case anythingElse                   => throw new IllegalStateException("The following Coq match item is not supported: " + anythingElse.toCoqCode)
    }

    private def convertPatternEquation(patternEquation: PatternEquation) =
      {
        val PatternEquation(multPatterns, outputTerm) = patternEquation
        withPatternNames(multPatterns.flatMap { case MultPattern(patterns) => patterns.flatMap(boundNames) }) {
          CASE(multPatterns.map(convertMultPattern).reduce(_ OR_PATTERN _)) ==> termToTreeHuggerAst(outputTerm)
        }
      }

    private def convertPatternEquationExpanded(patternEquation: PatternEquation): List[CaseDef] = {
      val PatternEquation(multPatterns, outputTerm) = patternEquation
      multPatterns.map { pattern =>
        val MultPattern(patterns) = pattern
        withPatternNames(patterns.flatMap(boundNames)) {
          CASE(convertMultPattern(pattern)) ==> termToTreeHuggerAst(outputTerm)
        }
      }
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

    def convertRecordInstance(instanceName: String, args: Option[Binders], recordType: Term, concreteRecordFields: List[ConcreteRecordField]): Tree = {

      def getNameAndArgsFrom(recordType: Term) = recordType match {
        case Qualid(List(Ident(name))) => (name, None)
        case UncurriedTermApplication(Qualid(List(Ident(name))), args) => (name, Some(args.map {
          case Argument(_, typeTerm) => typeTerm
        }))
        case ExplicitQualidApplication(Qualid(List(Ident(name))), args) => (name, Some(args))
        case anythingElse =>
          throw new IllegalStateException("Unsupported record instance return type: " + anythingElse.toCoqCode)
      }

      val (recordName, typeApps) = getNameAndArgsFrom(recordType)
      val abstractFields = fetchRecordAbstractFields(recordName)

      val binderTypeAliases = typeApps.fold[List[Tree]](List()) { typeArgs =>
        getNamesFromTypeParameter(fetchRecordBinders(recordName)).zip(typeArgs).map {
          case (Name(Some(id)), typeArg) => createTypeAliasDefinition(id, None) := coqTypeToTreeHuggerType(typeArg)
        }
      }

      val recordBlock = BLOCK(
        binderTypeAliases ++ concreteRecordFields.map {
          case ConcreteRecordField(name, implementedBinders, _, bodyTerm) =>
            val AbstractRecordField(abstractFieldName, definedBinders, typeTerm) = abstractFields(convertNameToString(name))

            val potentialException =
              new IllegalStateException("The method signatures of instance " + instanceName + " should conform to signatures defined in record " + recordType + ":\n" +
                implementedBinders.fold("()")(_.toCoqCode) + "\n" +
                "Differ from:\n" +
                definedBinders.fold("()")(_.toCoqCode))

            ConcreteRecordField(
              name,
              annotateParamsWithType(definedBinders, implementedBinders, potentialException),
              Some(typeTerm),
              bodyTerm)
        }.map(convertConcreteRecordField))

      val translatedRecordType = coqTypeToScalaCode(recordType)
      args.fold[Tree](
        OBJECTDEF(instanceName).withParents(List(translatedRecordType)) := recordBlock) {
          binders =>
            createDefinition(Ident(instanceName), Some(binders), Some(recordType)) :=
              NEW(
                ANONDEF(translatedRecordType) :=
                  recordBlock)
        }

    }

    private def annotateParamsWithType(definedBinders: Option[Binders], implementedBinders: Option[Binders], potentialException: Exception): Option[Binders] = {
      (definedBinders, implementedBinders) match {
        case (None, None)                   => None
        case (None, Some(Binders(binders))) => throw potentialException
        case (Some(Binders(binders)), None) => throw potentialException
        case (Some(Binders(defBinders)), Some(Binders(implBinders))) => {
          def expandBinders(binders: List[Binder]) = binders.flatMap {
            case ExplicitBinderWithType(names, typeTerm) => names.map(name => ExplicitBinderWithType(List(name), typeTerm))
            case ImplicitBinder(names, typeTerm)         => names.map(name => ImplicitBinder(List(name), typeTerm))
            case anthingElse                             => List(anthingElse)
          }

          val expandedDefBinders = expandBinders(defBinders)
          val expandedImplBinders = expandBinders(implBinders)

          if (expandedDefBinders.length != expandedImplBinders.length)
            throw potentialException

          Some(Binders(expandedDefBinders.zip(expandedImplBinders).map {
            case (ExplicitBinderWithType(List(_), typeTerm), ExplicitSimpleBinder(implName))           => ExplicitBinderWithType(List(implName), typeTerm)
            case (ImplicitBinder(List(_), typeTerm), ExplicitSimpleBinder(implName))                   => ImplicitBinder(List(implName), typeTerm)
            case (ImplicitBinder(List(_), typeTerm), ExplicitBinderWithType(implName, _))              => ImplicitBinder(implName, typeTerm)
            case (ExplicitBinderWithType(List(_), _), implBinder @ ExplicitBinderWithType(List(_), _)) => implBinder
            case (ImplicitBinder(List(_), _), implBinder @ ImplicitBinder(List(_), _))                 => implBinder
            case (defBinder, implBinder) =>
              throw new IllegalStateException(
                "Unexpected record definition parameter: " + defBinder.toCoqCode + "\n" +
                  "And corresponding record instance parameter: " + implBinder.toCoqCode)
          }))

        }
      }
    }

    private def fetchRecordAbstractFields(recordType: String): Map[String, AbstractRecordField] = (
      for {
        Record(_, Ident(recordName), _, (None | Some(Set | Type)), _, fields) <- coqTrees if (recordName == recordType)
        abstractField @ AbstractRecordField(fieldName, _, _) <- fields
      } yield (convertNameToString(fieldName) -> abstractField)).toMap

    private def fetchRecordBinders(recordType: String): List[Binder] =
      (for {
        Record(_, Ident(recordName), Some(Binders(binders)), (None | Some(Set | Type)), _, _) <- coqTrees if (recordName == recordType)
      } yield binders).flatten

    private def convertRecord(record: Record): Tree = {
      val Record(_, Ident(recordName), binders, (None | Some(Set | Type)), _, fields) = record: @unchecked

      TRAITDEF(recordName).withTypeParams(convertTypeBindersToTypeVars(binders)) :=
        BLOCK(
          fields.map(convertRecordField))
    }

    private def createRecordConstructionFunction(record: Record): Option[Tree] = {

      val constructor = computeRecordConstructorName(record)

      constructor.map { constructorName =>
        val Record(_, Ident(recordName), binders, (None | Some(Set | Type)), _, fields) = record: @unchecked
        val abstractFields = filterAbstractRecordFields(fields)

        val typeBinderParams = convertTypeBindersToTypeVars(binders)

        val recordType = createTypeWithGenericParams(recordName, typeBinderParams.map(typeVar => TYPE_REF(typeVar.name)))
        val declaration = DEF(constructorName, recordType)

        val (typeFields, valueFields) = abstractFields.partition(recordFieldIsTypeField)
        val typeFieldParams = convertTypeFieldsToTypeVars(typeFields)
        val valueFieldParams = convertValueFieldsToParams(valueFields)

        val namePrefix = recordName + "_"
        curryingStrategy.createDefinition(
          declaration.withTypeParams(typeBinderParams ::: typeFieldParams),
          valueFieldParams) := BLOCK(
            createFieldAliases(abstractFields, namePrefix) :+
              NEW(
                ANONDEF(recordType) :=
                  BLOCK(assignFieldAliasesToNewRecordAbstractField(abstractFields, namePrefix))))
      }
    }

    private def computeRecordConstructorName(record: Record): Option[String] = {
      val Record(_, Ident(recordName), _, (None | Some(Set | Type)), constructor, _) = record: @unchecked
      constructor.map { case Ident(constructorName) => constructorName }
    }

    private def filterAbstractRecordFields(fields: List[RecordField]): List[AbstractRecordField] =
      for { abstractField @ AbstractRecordField(_, _, _) <- fields } yield abstractField

    private def extractNameFromRecordField(field: RecordField): String = field match {
      case AbstractRecordField(name, _, _)    => convertNameToString(name)
      case ConcreteRecordField(name, _, _, _) => convertNameToString(name)
    }

    private def assignFieldAliasesToNewRecordAbstractField(abstractFields: List[AbstractRecordField], namePrefix: String) =
      (abstractFields zip abstractFields.map(recordFieldIsTypeField)) map {
        case (typefield, true)   => convertAbstractRecordField(typefield) := TYPE_REF(namePrefix + extractNameFromRecordField(typefield))
        case (valuefield, false) => convertAbstractRecordField(valuefield) := REF(namePrefix + extractNameFromRecordField(valuefield))
      }

    private def createFieldAliases(abstractFields: List[AbstractRecordField], namePrefix: String) =
      (abstractFields zip abstractFields.map(recordFieldIsTypeField)) map {
        case (typefield, true)   => createTypeFieldAlias(typefield, namePrefix)
        case (valuefield, false) => createValueFieldAlias(valuefield, namePrefix)
      }

    private def createTypeFieldAlias(typeField: RecordField, namePrefix: String) = {
      val name: String = extractNameFromRecordField(typeField)
      TYPEVAR(namePrefix + name) := TYPE_REF(name)
    }

    private def createValueFieldAlias(valueField: RecordField, namePrefix: String) = {
      val name: String = extractNameFromRecordField(valueField)
      DEF(namePrefix + name) := REF(name)
    }

    private def convertRecordField(recordField: RecordField): Tree = recordField match {
      case abstractRecordField @ AbstractRecordField(_, _, _) =>
        convertAbstractRecordField(abstractRecordField)
      case concreteRecordField @ ConcreteRecordField(_, _, _, _) =>
        convertConcreteRecordField(concreteRecordField)
    }

    private def convertAbstractRecordField(abstractRecordField: AbstractRecordField): Tree =
      (abstractRecordField, recordFieldIsTypeField(abstractRecordField)) match {
        case (AbstractRecordField(name, binders, Set | Type), true) =>
          createTypeAliasDefinition(convertNameToIdent(name), binders)
        case (AbstractRecordField(name, binders, typeTerm), false) =>
          createRecordFieldDefinition(name, binders, typeTerm)
        case (anythingElse, _) =>
          throw new IllegalStateException("This record field cannot be converted to Scala: " + anythingElse.toCoqCode)
      }

    private def convertConcreteRecordField(concreteRecordField: ConcreteRecordField): Tree =
      (concreteRecordField, recordFieldIsTypeField(concreteRecordField)) match {
        case (ConcreteRecordField(name, binders, Some(Set | Type), bodyTypeTerm), true) =>
          createTypeAliasDefinition(convertNameToIdent(name), binders) :=
            coqTypeToTreeHuggerType(bodyTypeTerm)
        case (ConcreteRecordField(name, binders, Some(typeTerm), bodyTerm), false) =>
          createRecordFieldDefinition(name, binders, typeTerm) :=
            binders.fold(
              termToTreeHuggerAst(bodyTerm)) {
                case Binders(params) =>
                  val valueParams = params.filter(binder => !isTypeBinder(binder))
                  if (valueParams.isEmpty)
                    termToTreeHuggerAst(bodyTerm)
                  else
                    createAnonymousFunction(Binders(valueParams), bodyTerm)
              }
        case (anythingElse, _) =>
          throw new IllegalStateException("This record field cannot be converted to Scala: " + anythingElse.toCoqCode)
      }

    private def createRecordFieldDefinition(name: Name, binders: Option[Binders], typeTerm: Term): Tree = {
      val (typeBinders, valueBinders) =
        binders.fold[(Option[Binders], Option[Binders])]((None, None)) {
          case Binders(params) =>
            val (typeBinders, valueBinders) = params.partition(isTypeBinder)
            (if (typeBinders.isEmpty) None else Some(Binders(typeBinders)),
              if (valueBinders.isEmpty) None else Some(Binders(valueBinders)))
        }
      val defWithoutTypeParams = DEF(convertNameToString(name), computeFunctionReturnType(valueBinders, typeTerm))

      typeBinders.fold(defWithoutTypeParams) {
        case Binders(typeParams) =>
          defWithoutTypeParams.withTypeParams(convertTypeBinders(typeParams))
      }

    }

    private def convertTypeFieldsToTypeVars(fields: List[AbstractRecordField]) =
      fields.map(field => TYPEVAR(extractNameFromRecordField(field)))

    private def convertValueFieldsToParams(fields: List[AbstractRecordField]) =
      for {
        AbstractRecordField(name, binders, typeTerm) <- fields
      } yield mkTreeFromDefStart(PARAM(convertNameToString(name), computeFunctionReturnType(binders, typeTerm)))

    private def computeFunctionReturnType(binders: Option[Binders], typeTerm: Term): Type = binders match {
      case Some(params) => convertBindersToFunctionReturnType(params) TYPE_=> coqTypeToTreeHuggerType(typeTerm)
      case None         => coqTypeToTreeHuggerType(typeTerm)
    }

    private def convertBindersToFunctionReturnType(binders: Binders): Type = {
      val Binders(params) = binders
      params.map {
        case ExplicitBinderWithType(names, typeTerm) => {
          val scalaType = coqTypeToTreeHuggerType(typeTerm)
          names.map(_ => scalaType).reduceRight(_ TYPE_=> _)
        }
        case param @ (ExplicitSimpleBinder(_) | ImplicitBinder(_, _)) =>
          throw new IllegalStateException("Illehgal abstract record field parameter: " + param.toCoqCode)
      }.reduceRight(_ TYPE_=> _)
    }
  }
}
