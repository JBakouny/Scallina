package scala.of.coq.parsercombinators

import scala.of.coq.parsercombinators.parser.CoqTermParser
import scala.of.coq.parsercombinators.parser.Argument
import scala.of.coq.parsercombinators.parser.BetweenParenthesis
import scala.of.coq.parsercombinators.parser.Binders
import scala.of.coq.parsercombinators.parser.ConstructorPattern
import scala.of.coq.parsercombinators.parser.DepRetType
import scala.of.coq.parsercombinators.parser.ExplicitBinderWithType
import scala.of.coq.parsercombinators.parser.Fix
import scala.of.coq.parsercombinators.parser.FixBodies
import scala.of.coq.parsercombinators.parser.FixBody
import scala.of.coq.parsercombinators.parser.ForAll
import scala.of.coq.parsercombinators.parser.Fun
import scala.of.coq.parsercombinators.parser.Ident
import scala.of.coq.parsercombinators.parser.ImplicitBinder
import scala.of.coq.parsercombinators.parser.LetConstructorArgsIn
import scala.of.coq.parsercombinators.parser.LetFixIn
import scala.of.coq.parsercombinators.parser.LetPatternIn
import scala.of.coq.parsercombinators.parser.Match
import scala.of.coq.parsercombinators.parser.MatchItem
import scala.of.coq.parsercombinators.parser.MultPattern
import scala.of.coq.parsercombinators.parser.Name
import scala.of.coq.parsercombinators.parser.Number
import scala.of.coq.parsercombinators.parser.NumberPattern
import scala.of.coq.parsercombinators.parser.OrPattern
import scala.of.coq.parsercombinators.parser.ParenthesisOrPattern
import scala.of.coq.parsercombinators.parser.PatternEquation
import scala.of.coq.parsercombinators.parser.Qualid
import scala.of.coq.parsercombinators.parser.QualidPattern
import scala.of.coq.parsercombinators.parser.ReturnType
import scala.of.coq.parsercombinators.parser.ExplicitSimpleBinder
import scala.of.coq.parsercombinators.parser.SimpleLetIn
import scala.of.coq.parsercombinators.parser.TermIf
import scala.of.coq.parsercombinators.parser.{ Term_% => Term_% }
import scala.of.coq.parsercombinators.parser.{ Term_-> => Term_-> }
import scala.of.coq.parsercombinators.parser.Type
import scala.of.coq.parsercombinators.parser.UncurriedTermApplication
import scala.of.coq.parsercombinators.parser.UnderscorePattern

import org.scalatest.Finders
import org.scalatest.FunSuite
import org.scalatest.Matchers.convertToAnyShouldWrapper

import CustomMatchers.parse

class CoqTermParserFileBasedTest extends FunSuite {

  def fileToString(fileName: String): String = {
    val fileBufferedSource = io.Source.fromURL(getClass.getResource("/TermFragments/" + fileName));
    try fileBufferedSource.mkString finally fileBufferedSource.close()
  }

  test("""Testing "forall a b c, (a -> b) -> (b -> c) -> (a -> c)" """) {
    CoqTermParser(fileToString("ForAllFragment.v")) should parse (
      ForAll(Binders(List(ExplicitSimpleBinder(Name(Some(Ident("a")))), ExplicitSimpleBinder(Name(Some(Ident("b")))), ExplicitSimpleBinder(Name(Some(Ident("c")))))),
        Term_->(BetweenParenthesis(Term_->(Qualid(List(Ident("a"))), Qualid(List(Ident("b"))))),
          Term_->(BetweenParenthesis(Term_->(Qualid(List(Ident("b"))), Qualid(List(Ident("c"))))),
            BetweenParenthesis(Term_->(Qualid(List(Ident("a"))), Qualid(List(Ident("c")))))))))
  }

  test("""Testing "fun s => 5" """) {
    CoqTermParser(fileToString("FunFragment.v")) should parse (Fun(Binders(List(
      ExplicitSimpleBinder(Name(Some(Ident("s")))))),
      Number(5)))
  }

  test("""Testing "fun {A : Type} (l r : A) => r" """) {
    CoqTermParser(fileToString("FunImplicitParamsFragment.v")) should parse (Fun(Binders(List(
      ImplicitBinder(List(Name(Some(Ident("A")))), Some(Type)),
      ExplicitBinderWithType(List(Name(Some(Ident("l"))), Name(Some(Ident("r")))), Qualid(List(Ident("A")))))),
      Qualid(List(Ident("r")))))
  }

  test("""Testing "fun (A : Type) (_ b _ : A) => b" """) {
    CoqTermParser(fileToString("TemplateFunFragment.v")) should parse (Fun(Binders(List(
      ExplicitBinderWithType(List(Name(Some(Ident("A")))), Type),
      ExplicitBinderWithType(List(Name(None), Name(Some(Ident("b"))), Name(None)),
        Qualid(List(Ident("A")))))),
      Qualid(List(Ident("b")))))
  }

  test("""Testing
          fix rightMost {A : Type} (t : BinTree) : A := match t with
           L x => x
          | N l r => rightMost r
          end
          """) {
    CoqTermParser(fileToString("FixFragment.v")) should parse(
      Fix(FixBodies(
        FixBody(Ident("rightMost"),
          Binders(List(
            ImplicitBinder(List(Name(Some(Ident("A")))), Some(Type)),
            ExplicitBinderWithType(List(Name(Some(Ident("t")))), Qualid(List(Ident("BinTree")))))),
          None,
          Some(Qualid(List(Ident("A")))),
          Match(List(
            MatchItem(Qualid(List(Ident("t"))), None, None)),
            None,
            List(
              PatternEquation(
                List(MultPattern(List(
                  ConstructorPattern(Qualid(List(Ident("L"))), List(QualidPattern(Qualid(List(Ident("x"))))))))),
                Qualid(List(Ident("x")))),
              PatternEquation(
                List(MultPattern(List(
                  ConstructorPattern(Qualid(List(Ident("N"))), List(QualidPattern(Qualid(List(Ident("l")))), QualidPattern(Qualid(List(Ident("r"))))))))),
                UncurriedTermApplication(Qualid(List(Ident("rightMost"))), List(Argument(None, Qualid(List(Ident("r"))))))))))))
    )
  }

  test("""Testing "let x := 3 in x" """) {
    CoqTermParser(fileToString("LetInFragment.v")) should parse(
      SimpleLetIn(
        Ident("x"), None, None,
        Number(3),
        Fun(Binders(List(ExplicitSimpleBinder(Name(Some(Ident("y")))))), Term_%(Qualid(List(Ident("y"))), Ident("x")))))
  }

  test("""Testing "let sumAlias (a b : nat) : nat := sum a b in sumAlias 3 7" """) {
    CoqTermParser(fileToString("LetInFunFragment.v")) should parse (
      SimpleLetIn(Ident("sumAlias"),
        Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("a"))), Name(Some(Ident("b")))), Qualid(List(Ident("nat"))))))),
        Some(Qualid(List(Ident("nat")))),
        UncurriedTermApplication(Qualid(List(Ident("sum"))), List(Argument(None, Qualid(List(Ident("a")))), Argument(None, Qualid(List(Ident("b")))))),
        UncurriedTermApplication(Qualid(List(Ident("sumAlias"))), List(Argument(None, Number(3)), Argument(None, Number(7))))))
  }

  test("""Testing "let fix right (l r : nat) := r in right 7 3" """) {
    CoqTermParser(fileToString("LetFixInFragment.v")) should parse (
      LetFixIn(
        FixBody(Ident("right"),
          Binders(List(
            ExplicitBinderWithType(List(Name(Some(Ident("l"))), Name(Some(Ident("r")))), Qualid(List(Ident("nat")))))),
          None,
          None,
          Qualid(List(Ident("r")))),
        UncurriedTermApplication(
          Qualid(List(Ident("right"))),
          List(Argument(None, Number(7)), Argument(None, Number(3)))))
    )
  }

  test("""Testing "let (l, r) return nat := Node 3 7 in sum l r" """) {
    CoqTermParser(fileToString("LetConstructorInFragment.v")) should parse(LetConstructorArgsIn(
      List(Name(Some(Ident("l"))), Name(Some(Ident("r")))),
      Some(DepRetType(None, ReturnType(Qualid(List(Ident("nat")))))),
      UncurriedTermApplication(Qualid(List(Ident("Node"))), List(Argument(None, Number(3)), Argument(None, Number(7)))),
      UncurriedTermApplication(Qualid(List(Ident("sum"))), List(Argument(None, Qualid(List(Ident("l")))), Argument(None, Qualid(List(Ident("r"))))))))
  }

  test("""Testing "let 'pair (pair l0 r0) (pair l1 r1) := pair (pair 3 5) (pair 7 10) return nat in sum (sum l0 r0) (sum l1 r1)" """) {
    CoqTermParser(fileToString("LetPatternInFragment.v")) should parse (
      LetPatternIn(
        ConstructorPattern(
          Qualid(List(Ident("pair"))),
          List(
            ParenthesisOrPattern(
              List(OrPattern(List(
                ConstructorPattern(
                  Qualid(List(Ident("pair"))),
                  List(
                    QualidPattern(Qualid(List(Ident("l0")))),
                    QualidPattern(Qualid(List(Ident("r0")))))))))),
            ParenthesisOrPattern(
              List(OrPattern(List(
                ConstructorPattern(
                  Qualid(List(Ident("pair"))),
                  List(
                    QualidPattern(Qualid(List(Ident("l1")))),
                    QualidPattern(Qualid(List(Ident("r1")))))))))))),
        UncurriedTermApplication(
          Qualid(List(Ident("pair"))),
          List(
            Argument(None,
              BetweenParenthesis(
                UncurriedTermApplication(
                  Qualid(List(Ident("pair"))),
                  List(
                    Argument(None, Number(3)),
                    Argument(None, Number(5)))))),
            Argument(None,
              BetweenParenthesis(
                UncurriedTermApplication(
                  Qualid(List(Ident("pair"))),
                  List(
                    Argument(None, Number(7)),
                    Argument(None, Number(10)))))))),
        Some(ReturnType(Qualid(List(Ident("nat"))))),
        UncurriedTermApplication(
          Qualid(List(Ident("sum"))),
          List(
            Argument(None,
              BetweenParenthesis(
                UncurriedTermApplication(
                  Qualid(List(Ident("sum"))),
                  List(
                    Argument(None, Qualid(List(Ident("l0")))),
                    Argument(None, Qualid(List(Ident("r0")))))))),
            Argument(None,
              BetweenParenthesis(
                UncurriedTermApplication(
                  Qualid(List(Ident("sum"))),
                  List(
                    Argument(None, Qualid(List(Ident("l1")))),
                    Argument(None, Qualid(List(Ident("r1"))))))))))))
  }

  test("""Testing "if a then 5 else 7" """) {
    CoqTermParser(fileToString("IfFragment.v")) should parse (TermIf(Qualid(List(Ident("a"))), None, Number(5), Number(7)))
  }

  test("""Testing "sum (x := 7) 3" """) {
    CoqTermParser(fileToString("ApplicationFragment.v")) should parse(
      UncurriedTermApplication(
        Qualid(List(Ident("sum"))),
        List(
          Argument(Some(Ident("x")), Number(7)),
          Argument(None, Number(3)))))
  }

  test("""Testing "sum 7 3" """) {
    CoqTermParser(fileToString("SimpleApplicationFragment.v")) should parse(
      UncurriedTermApplication(
        Qualid(List(Ident("sum"))),
        List(
          Argument(None, Number(7)),
          Argument(None, Number(3)))))
  }

  test("""Testing "sum (S 0) 0" """) {
    CoqTermParser(fileToString("ApplicationOnApplicationFragment.v")) should parse(
      UncurriedTermApplication(
        Qualid(List(Ident("sum"))),
        List(
          Argument(None, BetweenParenthesis(UncurriedTermApplication(Qualid(List(Ident("S"))), List(Argument(None, Number(0)))))),
          Argument(None, Number(0)))))
  }

  test("""
          Testing the below:
          match pair 3 7 return nat with
            pair x 7 => x
          | pair _ y => y
          end
          """) {

    CoqTermParser(fileToString("SimplePatternMatchFragment.v")) should parse (
      Match(List(
        MatchItem(
          UncurriedTermApplication(Qualid(List(Ident("pair"))),
            List(Argument(None, Number(3)), Argument(None, Number(7)))),
          None,
          None)),
        Some(ReturnType(Qualid(List(Ident("nat"))))),
        List(
          PatternEquation(
            List(
              MultPattern(List(ConstructorPattern(Qualid(List(Ident("pair"))), List(QualidPattern(Qualid(List(Ident("x")))), NumberPattern(Number(7))))))),
            Qualid(List(Ident("x")))),
          PatternEquation(
            List(
              MultPattern(List(ConstructorPattern(Qualid(List(Ident("pair"))), List(UnderscorePattern, QualidPattern(Qualid(List(Ident("y"))))))))),
            Qualid(List(Ident("y"))))))
    )
  }

  test(""" Testing
    match k with
      0 => None
    | S k1 =>
      match n with
        0 => Some 0
      | 1 => Some 1
      | n => None
      end
    end
    """) {

    CoqTermParser(fileToString("EmbeddedPatternMatchFragment.v")) should parse (
      Match(List(
        MatchItem(Qualid(List(Ident("k"))), None, None)),
        None,
        List(
          PatternEquation(List(MultPattern(List(NumberPattern(Number(0))))),
            Qualid(List(Ident("None")))),
          PatternEquation(List(MultPattern(List(ConstructorPattern(Qualid(List(Ident("S"))), List(QualidPattern(Qualid(List(Ident("k1"))))))))),
            Match(List(
              MatchItem(Qualid(List(Ident("n"))), None, None)),
              None,
              List(
                PatternEquation(List(MultPattern(List(NumberPattern(Number(0))))),
                  UncurriedTermApplication(Qualid(List(Ident("Some"))), List(Argument(None, Number(0))))),
                PatternEquation(List(MultPattern(List(NumberPattern(Number(1))))),
                  UncurriedTermApplication(Qualid(List(Ident("Some"))), List(Argument(None, Number(1))))),
                PatternEquation(List(MultPattern(List(QualidPattern(Qualid(List(Ident("n"))))))),
                  Qualid(List(Ident("None")))))))))
    )

  }

  test(""" Testing
    match Node (Node Leaf Leaf) Leaf, Leaf with
      Leaf, Leaf  => Leaf
    | Node l r, Leaf => l
    | Leaf, Node l r => r
    | Node l _, Node _ r => Node l r
    end
    """) {

    CoqTermParser(fileToString("TwoItemsPatternMatchFragment.v")) should parse (
      Match(List(
        MatchItem(
          UncurriedTermApplication(Qualid(List(Ident("Node"))),
            List(
              Argument(None, BetweenParenthesis(
                UncurriedTermApplication(Qualid(List(Ident("Node"))),
                  List(
                    Argument(None, Qualid(List(Ident("Leaf")))),
                    Argument(None, Qualid(List(Ident("Leaf")))))))),
              Argument(None, Qualid(List(Ident("Leaf")))))),
          None,
          None),
        MatchItem(
          Qualid(List(Ident("Leaf"))),
          None,
          None)),
        None,
        List(
          PatternEquation(
            List(MultPattern(List(
              QualidPattern(Qualid(List(Ident("Leaf")))),
              QualidPattern(Qualid(List(Ident("Leaf"))))))),
            Qualid(List(Ident("Leaf")))),
          PatternEquation(
            List(MultPattern(List(
              ConstructorPattern(Qualid(List(Ident("Node"))), List(QualidPattern(Qualid(List(Ident("l")))), QualidPattern(Qualid(List(Ident("r")))))),
              QualidPattern(Qualid(List(Ident("Leaf"))))))),
            Qualid(List(Ident("l")))),
          PatternEquation(
            List(MultPattern(List(
              QualidPattern(Qualid(List(Ident("Leaf")))),
              ConstructorPattern(Qualid(List(Ident("Node"))), List(QualidPattern(Qualid(List(Ident("l")))), QualidPattern(Qualid(List(Ident("r"))))))))),
            Qualid(List(Ident("r")))),
          PatternEquation(
            List(MultPattern(List(
              ConstructorPattern(Qualid(List(Ident("Node"))), List(QualidPattern(Qualid(List(Ident("l")))), UnderscorePattern)),
              ConstructorPattern(Qualid(List(Ident("Node"))), List(UnderscorePattern, QualidPattern(Qualid(List(Ident("r"))))))))),
            UncurriedTermApplication(Qualid(List(Ident("Node"))), List(Argument(None, Qualid(List(Ident("l")))), Argument(None, Qualid(List(Ident("r"))))))))))

  }

  test(""" Testing
      match Node (Node Leaf Leaf) (Node Leaf Leaf) as c with
        Leaf  => Leaf
      | c => Node Leaf Leaf
      end
    """) {

    CoqTermParser(fileToString("NamedPatternMatchFragment.v")) should parse (
      Match(List(
        MatchItem(
          UncurriedTermApplication(Qualid(List(Ident("Node"))),
            List(
              Argument(None, BetweenParenthesis(UncurriedTermApplication(Qualid(List(Ident("Node"))),
                List(Argument(None, Qualid(List(Ident("Leaf")))), Argument(None, Qualid(List(Ident("Leaf")))))))),
              Argument(None, BetweenParenthesis(UncurriedTermApplication(Qualid(List(Ident("Node"))),
                List(Argument(None, Qualid(List(Ident("Leaf")))), Argument(None, Qualid(List(Ident("Leaf")))))))))),
          Some(Name(Some(Ident("c")))),
          None)),
        None,
        List(
          PatternEquation(List(MultPattern(List(
            QualidPattern(Qualid(List(Ident("Leaf"))))))),
            Qualid(List(Ident("Leaf")))),
          PatternEquation(List(MultPattern(List(
            QualidPattern(Qualid(List(Ident("c"))))))),
            UncurriedTermApplication(Qualid(List(Ident("Node"))),
              List(
                Argument(None, Qualid(List(Ident("Leaf")))),
                Argument(None, Qualid(List(Ident("Leaf"))))))))))

  }

}
