package scala.of.coq.parsercombinators

import scala.of.coq.parsercombinators.parser.Binders
import scala.of.coq.parsercombinators.parser.CoqParser
import scala.of.coq.parsercombinators.parser.Definition
import scala.of.coq.parsercombinators.parser.ExplicitBinderWithType
import scala.of.coq.parsercombinators.parser.Ident
import scala.of.coq.parsercombinators.parser.ImplicitBinder
import scala.of.coq.parsercombinators.parser._
import scala.of.coq.parsercombinators.parser.Qualid
import scala.of.coq.parsercombinators.parser.Type

import org.scalatest.Finders
import org.scalatest.FunSuite
import org.scalatest.Matchers.convertToAnyShouldWrapper

import CustomMatchers.parse

class CoqParserTest extends FunSuite {

  test("""Testing "Require Import Coq.Arith.PeanoNat." """) {
    CoqParser("Require Import Coq.Arith.PeanoNat.") should parse(
      List(RequireImport(Qualid(List(Ident("Coq"), Ident("Arith"), Ident("PeanoNat")))))
    )
  }

  test("""Testing "Arguments Leaf {A} _." """) {
    CoqParser("Arguments Leaf {A} _.") should parse(
      List(ArgumentsCommand(Qualid(List(Ident("Leaf"))), Binders(List(ImplicitBinder(List(Name(Some(Ident("A")))), None), ExplicitSimpleBinder(Name(None))))))
    )
  }

  test("""Testing "Local Open Scope Z_scope." """) {
    CoqParser("Local Open Scope Z_scope.") should parse(
      List(ScopeCommand(Qualid(List(Ident("Z_scope"))), true))
    )
  }

  test("""Testing "Open Scope Z_scope." """) {
    CoqParser("Open Scope Z_scope.") should parse(
      List(ScopeCommand(Qualid(List(Ident("Z_scope"))), false))
    )
  }

  test("""Testing "Definition constantDef := 3." """) {
    CoqParser("Definition constantDef := 3.") should parse(
      List(Definition(Ident("constantDef"), None, None, Number(3)))
    )
  }

  test("""Testing the support of (* Coq comments *) """) {
    CoqParser("""
      (* Coq comments are supported by this parser *)

      (* They can be inserted before a code instruction *)

      Definition constantDef := (* In the middle of an instruction *) 7.

      (* or at the end of an instruction *)
      """) should parse(
      List(Definition(Ident("constantDef"), None, None, Number(7)))
    )
  }

  test("""Testing "Definition constantDef : nat := 3." """) {
    CoqParser("Definition constantDef : nat := 3.") should parse(
      List(Definition(Ident("constantDef"), None, Some(Qualid(List(Ident("nat")))), Number(3)))
    )
  }

  test("""Testing "Definition sum(a b: nat) := a + b." """) {
    CoqParser("Definition sum(a b: nat) := a + b.") should parse(
      List(
        Definition(Ident("sum"),
          Some(Binders(List(
            ExplicitBinderWithType(
              List(
                Name(Some(Ident("a"))),
                Name(Some(Ident("b")))),
              Qualid(List(Ident("nat"))))))),
          None,
          InfixOperator(Qualid(List(Ident("a"))), "+", Qualid(List(Ident("b"))))))
    )
  }

  test("""Testing "Definition right {A : Type} (a b : A) := a." """) {
    CoqParser("Definition right {A : Type} (a b : A) := a.") should parse(
      List(
        Definition(
          Ident("right"),
          Some(Binders(List(
            ImplicitBinder(List(Name(Some(Ident("A")))), Some(Type)),
            ExplicitBinderWithType(List(Name(Some(Ident("a"))), Name(Some(Ident("b")))), Qualid(List(Ident("A"))))))),
          None,
          Qualid(List(Ident("a")))))
    )
  }

  test("""Testing "Definition right {A : Type} (a b : A) : A := a." """) {
    CoqParser("Definition right {A : Type} (a b : A) : A := a.") should parse(
      List(
        Definition(
          Ident("right"),
          Some(Binders(List(
            ImplicitBinder(List(Name(Some(Ident("A")))), Some(Type)),
            ExplicitBinderWithType(List(Name(Some(Ident("a"))), Name(Some(Ident("b")))), Qualid(List(Ident("A"))))))),
          Some(Qualid(List(Ident("A")))),
          Qualid(List(Ident("a")))))
    )
  }

  test("""Testing "Definition right {A} (a b : A) : A := a." """) {
    CoqParser("Definition right {A} (a b : A) : A := a.") should parse(
      List(
        Definition(
          Ident("right"),
          Some(Binders(List(
            ImplicitBinder(List(Name(Some(Ident("A")))), None),
            ExplicitBinderWithType(List(Name(Some(Ident("a"))), Name(Some(Ident("b")))), Qualid(List(Ident("A"))))))),
          Some(Qualid(List(Ident("A")))),
          Qualid(List(Ident("a")))))
    )
  }

  test("""Testing
      Definition ListQueue : Queue := {|
        t := list nat;
        empty := nil;
        push x l := x :: l;
        pop := fun l =>
          match rev l with
            | nil => None
            | hd :: tl => Some (hd, rev tl)
          end
      |}.
    """) {
    CoqParser("""
      Definition ListQueue : Queue := {|
        t := list nat;
        empty := nil;
        push x l := x :: l;
        pop := fun l =>
          match rev l with
            | nil => None
            | hd :: tl => Some (hd, rev tl)
          end
      |}.
      """) should parse(
      List(
        Definition(
          Ident("ListQueue"),
          None,
          Some(Qualid(List(Ident("Queue")))),
          RecordInstantiation(
            List(
              ConcreteRecordField(Name(Some(Ident("t"))), None, None,
                UncurriedTermApplication(Qualid(List(Ident("list"))), List(Argument(None, Qualid(List(Ident("nat"))))))),
              ConcreteRecordField(Name(Some(Ident("empty"))), None, None,
                Qualid(List(Ident("nil")))),
              ConcreteRecordField(Name(Some(Ident("push"))), Some(Binders(List(ExplicitSimpleBinder(Name(Some(Ident("x")))), ExplicitSimpleBinder(Name(Some(Ident("l"))))))), None,
                InfixOperator(Qualid(List(Ident("x"))), "::", Qualid(List(Ident("l"))))),
              ConcreteRecordField(Name(Some(Ident("pop"))), None, None,
                Fun(
                  Binders(List(ExplicitSimpleBinder(Name(Some(Ident("l")))))),
                  Match(List(
                    MatchItem(UncurriedTermApplication(Qualid(List(Ident("rev"))), List(Argument(None, Qualid(List(Ident("l")))))), None, None)), None,
                    List(
                      PatternEquation(List(MultPattern(List(QualidPattern(Qualid(List(Ident("nil"))))))),
                        Qualid(List(Ident("None")))),
                      PatternEquation(List(MultPattern(List(InfixPattern(QualidPattern(Qualid(List(Ident("hd")))), "::", QualidPattern(Qualid(List(Ident("tl")))))))),
                        UncurriedTermApplication(Qualid(List(Ident("Some"))), List(Argument(None, TupleValue(List(Qualid(List(Ident("hd"))), UncurriedTermApplication(Qualid(List(Ident("rev"))), List(Argument(None, Qualid(List(Ident("tl"))))))))))))))))))))
    )
  }

  test("""Testing
    Inductive Tree : Type :=
      Leaf : Tree
    | Node(l r : Tree): Tree.
    """) {
    CoqParser("""
              Inductive Tree : Type :=
                Leaf : Tree
              | Node(l r : Tree): Tree.
              """) should parse(
      List(
        Inductive(
          InductiveBody(Ident("Tree"), None, Some(Type),
            List(
              InductiveBodyItem(Ident("Leaf"),
                None,
                Some(Qualid(List(Ident("Tree"))))),
              InductiveBodyItem(Ident("Node"),
                Some(Binders(List(
                  ExplicitBinderWithType(List(Name(Some(Ident("l"))), Name(Some(Ident("r")))), Qualid(List(Ident("Tree"))))))),
                Some(Qualid(List(Ident("Tree")))))))))

    )
  }

  test("""Testing
    Inductive Tree :=
      Leaf : Tree
    | Node(l r : Tree): Tree.
    """) {
    CoqParser("""
              Inductive Tree :=
                Leaf : Tree
              | Node(l r : Tree): Tree.
              """) should parse(
      List(
        Inductive(
          InductiveBody(Ident("Tree"), None, None,
            List(
              InductiveBodyItem(Ident("Leaf"),
                None,
                Some(Qualid(List(Ident("Tree"))))),
              InductiveBodyItem(Ident("Node"),
                Some(Binders(List(
                  ExplicitBinderWithType(List(Name(Some(Ident("l"))), Name(Some(Ident("r")))), Qualid(List(Ident("Tree"))))))),
                Some(Qualid(List(Ident("Tree")))))))))

    )
  }

  test("""Testing
    Inductive Tree :=
      Leaf
    | Node(l r : Tree).
    """) {
    CoqParser("""
              Inductive Tree :=
                Leaf
              | Node(l r : Tree).
              """) should parse(
      List(
        Inductive(
          InductiveBody(Ident("Tree"), None, None,
            List(
              InductiveBodyItem(Ident("Leaf"),
                None,
                None),
              InductiveBodyItem(Ident("Node"),
                Some(Binders(List(
                  ExplicitBinderWithType(List(Name(Some(Ident("l"))), Name(Some(Ident("r")))), Qualid(List(Ident("Tree"))))))),
                None)))))

    )
  }

  test("""Testing
    Inductive Tree {A B : Type} :=
    | Leaf (value: A)
    | Node (info: B) (left: Tree) (right: Tree).
    """) {
    CoqParser("""
              Inductive Tree {A B : Type} :=
              | Leaf (value: A)
              | Node (info: B) (left: Tree) (right: Tree).
              """) should parse(
      List(
        Inductive(
          InductiveBody(
            Ident("Tree"),
            Some(Binders(List(
              ImplicitBinder(
                List(
                  Name(Some(Ident("A"))),
                  Name(Some(Ident("B")))),
                Some(Type))))),
            None,
            List(
              InductiveBodyItem(Ident("Leaf"),
                Some(Binders(List(
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("value")))),
                    Qualid(List(Ident("A"))))))),
                None),
              InductiveBodyItem(Ident("Node"),
                Some(Binders(List(
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("info")))),
                    Qualid(List(Ident("B")))),
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("left")))),
                    Qualid(List(Ident("Tree")))),
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("right")))),
                    Qualid(List(Ident("Tree"))))))),
                None)))))

    )
  }

  test("""Testing
    Inductive Tree {A B : Type} : Type :=
    | Leaf (value: A) : Tree
    | Node (info: B) (left: Tree) (right: Tree) : Tree.
    """) {
    CoqParser("""
              Inductive Tree {A B : Type} : Type :=
              | Leaf (value: A) : Tree
              | Node (info: B) (left: Tree) (right: Tree) : Tree.
              """) should parse(
      List(
        Inductive(
          InductiveBody(
            Ident("Tree"),
            Some(Binders(List(
              ImplicitBinder(
                List(
                  Name(Some(Ident("A"))),
                  Name(Some(Ident("B")))),
                Some(Type))))),
            Some(Type),
            List(
              InductiveBodyItem(Ident("Leaf"),
                Some(Binders(List(
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("value")))),
                    Qualid(List(Ident("A"))))))),
                Some(Qualid(List(Ident("Tree"))))),
              InductiveBodyItem(Ident("Node"),
                Some(Binders(List(
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("info")))),
                    Qualid(List(Ident("B")))),
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("left")))),
                    Qualid(List(Ident("Tree")))),
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("right")))),
                    Qualid(List(Ident("Tree"))))))),
                Some(Qualid(List(Ident("Tree")))))))))

    )
  }

  test("""Testing
    Inductive tree {A B : Type} :=
    | Leaf (value: A)
    | Node (info: B) (left: @tree A B) (right: @tree A B).
    """) {
    CoqParser("""
              Inductive tree {A B : Type} :=
              | Leaf (value: A)
              | Node (info: B) (left: @tree A B) (right: @tree A B).
              """) should parse(
      List(
        Inductive(
          InductiveBody(
            Ident("tree"),
            Some(Binders(List(
              ImplicitBinder(
                List(
                  Name(Some(Ident("A"))),
                  Name(Some(Ident("B")))),
                Some(Type))))),
            None,
            List(
              InductiveBodyItem(Ident("Leaf"),
                Some(Binders(List(
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("value")))),
                    Qualid(List(Ident("A"))))))),
                None),
              InductiveBodyItem(Ident("Node"),
                Some(Binders(List(
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("info")))),
                    Qualid(List(Ident("B")))),
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("left")))),
                    ExplicitQualidApplication(
                      Qualid(List(Ident("tree"))),
                      List(
                        Qualid(List(Ident("A"))),
                        Qualid(List(Ident("B")))))),
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("right")))),
                    ExplicitQualidApplication(
                      Qualid(List(Ident("tree"))),
                      List(
                        Qualid(List(Ident("A"))),
                        Qualid(List(Ident("B"))))))))),
                None)))))
    )
  }

  test("""Testing
    Inductive tree {A B} :=
    | Leaf (value: A)
    | Node (info: B) (left: @tree A B) (right: @tree A B).
    """) {
    CoqParser("""
              Inductive tree {A B} :=
              | Leaf (value: A)
              | Node (info: B) (left: @tree A B) (right: @tree A B).
              """) should parse(
      List(
        Inductive(
          InductiveBody(
            Ident("tree"),
            Some(Binders(List(
              ImplicitBinder(
                List(
                  Name(Some(Ident("A"))),
                  Name(Some(Ident("B")))),
                None)))),
            None,
            List(
              InductiveBodyItem(Ident("Leaf"),
                Some(Binders(List(
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("value")))),
                    Qualid(List(Ident("A"))))))),
                None),
              InductiveBodyItem(Ident("Node"),
                Some(Binders(List(
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("info")))),
                    Qualid(List(Ident("B")))),
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("left")))),
                    ExplicitQualidApplication(
                      Qualid(List(Ident("tree"))),
                      List(
                        Qualid(List(Ident("A"))),
                        Qualid(List(Ident("B")))))),
                  ExplicitBinderWithType(List(
                    Name(Some(Ident("right")))),
                    ExplicitQualidApplication(
                      Qualid(List(Ident("tree"))),
                      List(
                        Qualid(List(Ident("A"))),
                        Qualid(List(Ident("B"))))))))),
                None)))))

    )
  }

  test("""Testing
      Record Queue :=
      {
        T : Type;
        empty : T;
        push : nat -> T -> T;
        pop : T -> option (nat * T)
      }.
    """) {
    CoqParser("""
              Record Queue :=
              {
                T : Type;
                empty : T;
                push : nat -> T -> T;
                pop : T -> option (nat * T)
              }.
              """) should parse(
      List(
        Record(
          RecordKeyword, Ident("Queue"),
          None, None, None,
          List(
            AbstractRecordField(Name(Some(Ident("T"))), None, Type),
            AbstractRecordField(Name(Some(Ident("empty"))), None, Qualid(List(Ident("T")))),
            AbstractRecordField(
              Name(Some(Ident("push"))), None,
              Term_->(
                Qualid(List(Ident("nat"))),
                Term_->(Qualid(List(Ident("T"))), Qualid(List(Ident("T"))))
              )
            ),
            AbstractRecordField(
              Name(Some(Ident("pop"))), None,
              Term_->(
                Qualid(List(Ident("T"))),
                UncurriedTermApplication(
                  Qualid(List(Ident("option"))),
                  List(
                    Argument(None, BetweenParenthesis(InfixOperator(Qualid(List(Ident("nat"))), "*", Qualid(List(Ident("T"))))))))
              )
            )
          )
        )
      )
    )
  }

  test("""Testing
      Structure Queue :=
      {
        T : Type;
        empty : T;
        push : nat -> T -> T;
        pop : T -> option (nat * T)
      }.
    """) {
    CoqParser("""
              Structure Queue :=
              {
                T : Type;
                empty : T;
                push : nat -> T -> T;
                pop : T -> option (nat * T)
              }.
              """) should parse(
      List(
        Record(
          StructureKeyword, Ident("Queue"),
          None, None, None,
          List(
            AbstractRecordField(Name(Some(Ident("T"))), None, Type),
            AbstractRecordField(Name(Some(Ident("empty"))), None, Qualid(List(Ident("T")))),
            AbstractRecordField(
              Name(Some(Ident("push"))), None,
              Term_->(
                Qualid(List(Ident("nat"))),
                Term_->(Qualid(List(Ident("T"))), Qualid(List(Ident("T"))))
              )
            ),
            AbstractRecordField(
              Name(Some(Ident("pop"))), None,
              Term_->(
                Qualid(List(Ident("T"))),
                UncurriedTermApplication(
                  Qualid(List(Ident("option"))),
                  List(
                    Argument(None, BetweenParenthesis(InfixOperator(Qualid(List(Ident("nat"))), "*", Qualid(List(Ident("T"))))))))
              )
            )
          )
        )
      )
    )
  }

  // TODO (Joseph Bakouny): Inductive records are currently not supported.
  ignore("""Testing
      Inductive Queue :=
      {
        T : Type;
        push : nat -> T -> T
      }.
    """) {
    CoqParser("""
              Inductive Queue :=
              {
                T : Type;
                push : nat -> T -> T
              }.
              """) should parse(
      List(
        Record(
          InductiveRecordKeyword, Ident("Queue"),
          None, None, None,
          List(
            AbstractRecordField(Name(Some(Ident("T"))), None, Type),
            AbstractRecordField(
              Name(Some(Ident("push"))), None,
              Term_->(
                Qualid(List(Ident("nat"))),
                Term_->(Qualid(List(Ident("T"))), Qualid(List(Ident("T"))))
              )
            )
          )
        )
      )
    )
  }

  // TODO (Joseph Bakouny): CoInductive records are currently not supported.
  ignore("""Testing
      CoInductive Queue :=
      {
        T : Type;
        push : nat -> T -> T
      }.
    """) {
    CoqParser("""
              CoInductive Queue :=
              {
                T : Type;
                push : nat -> T -> T
              }.
              """) should parse(
      List(
        Record(
          CoInductiveRecordKeyword, Ident("Queue"),
          None, None, None,
          List(
            AbstractRecordField(Name(Some(Ident("T"))), None, Type),
            AbstractRecordField(
              Name(Some(Ident("push"))), None,
              Term_->(
                Qualid(List(Ident("nat"))),
                Term_->(Qualid(List(Ident("T"))), Qualid(List(Ident("T"))))
              )
            )
          )
        )
      )
    )
  }

  test("""Testing
    Record TestRecord :=
    {
      testAbstractField (x: nat) : nat;
      testConcreteField (x: nat) : nat := x
    }.
    """) {
    CoqParser("""
              Record TestRecord :=
              {
                testAbstractField (x: nat) : nat;
                testConcreteField (x: nat) : nat := x
              }.
              """) should parse(
      List(
        Record(
          RecordKeyword, Ident("TestRecord"),
          None, None, None,
          List(
            AbstractRecordField(
              Name(Some(Ident("testAbstractField"))),
              Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat"))))))),
              Qualid(List(Ident("nat")))
            ),
            ConcreteRecordField(
              Name(Some(Ident("testConcreteField"))),
              Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat"))))))),
              Some(Qualid(List(Ident("nat")))),
              Qualid(List(Ident("x")))
            )
          )
        )
      )
    )
  }

  test("""Testing
    Record TestRecord :=
    {
      testAbstractField (x: nat) : nat;
      testConcreteField (x: nat) := x
    }.
    """) {
    CoqParser("""
              Record TestRecord :=
              {
                testAbstractField (x: nat) : nat;
                testConcreteField (x: nat) := x
              }.
              """) should parse(
      List(
        Record(
          RecordKeyword, Ident("TestRecord"),
          None, None, None,
          List(
            AbstractRecordField(
              Name(Some(Ident("testAbstractField"))),
              Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat"))))))),
              Qualid(List(Ident("nat")))
            ),
            ConcreteRecordField(
              Name(Some(Ident("testConcreteField"))),
              Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat"))))))),
              None,
              Qualid(List(Ident("x")))
            )
          )
        )
      )
    )
  }

  test("""Testing
    Record TestRecord : Type :=
    {
      testAbstractField (x: nat) : nat;
      testConcreteField (x: nat) := x
    }.
    """) {
    CoqParser("""
              Record TestRecord : Type :=
              {
                testAbstractField (x: nat) : nat;
                testConcreteField (x: nat) := x
              }.
              """) should parse(
      List(
        Record(
          RecordKeyword, Ident("TestRecord"),
          None, Some(Type), None,
          List(
            AbstractRecordField(
              Name(Some(Ident("testAbstractField"))),
              Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat"))))))),
              Qualid(List(Ident("nat")))
            ),
            ConcreteRecordField(
              Name(Some(Ident("testConcreteField"))),
              Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat"))))))),
              None,
              Qualid(List(Ident("x")))
            )
          )
        )
      )
    )
  }

  test("""Testing
    Record TestRecord (y: nat) :=
    {
      testAbstractField (x: nat) : nat;
      testConcreteField (x: nat) := x + y
    }.
    """) {
    CoqParser("""
              Record TestRecord (y: nat) :=
              {
                testAbstractField (x: nat) : nat;
                testConcreteField (x: nat) := x + y
              }.
              """) should parse(
      List(
        Record(
          RecordKeyword, Ident("TestRecord"),
          Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("y")))), Qualid(List(Ident("nat"))))))),
          None, None,
          List(
            AbstractRecordField(
              Name(Some(Ident("testAbstractField"))),
              Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat"))))))),
              Qualid(List(Ident("nat")))
            ),
            ConcreteRecordField(
              Name(Some(Ident("testConcreteField"))),
              Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat"))))))),
              None,
              InfixOperator(Qualid(List(Ident("x"))), "+", Qualid(List(Ident("y"))))
            )
          )
        )
      )
    )
  }

  test("""Testing
          Record TestRecord {A} :=
          {
            testAbstractField (x: A) : A;
            testConcreteField (x: A) := x
          }.
    """) {
    CoqParser("""
              Record TestRecord {A} :=
              {
                testAbstractField (x: A) : A;
                testConcreteField (x: A) := x
              }.
              """) should parse(
      List(
        Record(
          RecordKeyword, Ident("TestRecord"),
          Some(Binders(List(ImplicitBinder(List(Name(Some(Ident("A")))), None)))),
          None, None,
          List(
            AbstractRecordField(
              Name(Some(Ident("testAbstractField"))),
              Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("A"))))))),
              Qualid(List(Ident("A")))
            ),
            ConcreteRecordField(
              Name(Some(Ident("testConcreteField"))),
              Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("A"))))))),
              None,
              Qualid(List(Ident("x")))
            )
          )
        )
      )
    )
  }

  test("""Testing
    Record TestRecord :=
    {
      _ : nat;
      testConcreteField := 1
    }.
    """) {
    CoqParser("""
              Record TestRecord :=
              {
                _ : nat;
                testConcreteField := 1
              }.
              """) should parse(
      List(
        Record(
          RecordKeyword, Ident("TestRecord"),
          None, None, None,
          List(
            AbstractRecordField(
              Name(None),
              None,
              Qualid(List(Ident("nat")))
            ),
            ConcreteRecordField(
              Name(Some(Ident("testConcreteField"))),
              None,
              None,
              Number(1)
            )
          )
        )
      )
    )
  }

  test("""Testing
        Record TestRecord {A B} :=
        newTestRecord {
          f1 : A;
          f2 : B -> A
        }.

        Definition testRecordInstance := newTestRecord nat bool 7 (fun (b: bool) => if b then 3 else 17).
    """) {
    CoqParser("""
              Record TestRecord {A B} :=
              newTestRecord {
                f1 : A;
                f2 : B -> A
              }.

              Definition testRecordInstance := newTestRecord nat bool 7 (fun (b: bool) => if b then 3 else 17).
              """) should parse(
      List(
        Record(
          RecordKeyword, Ident("TestRecord"),
          Some(Binders(List(ImplicitBinder(List(Name(Some(Ident("A"))), Name(Some(Ident("B")))), None)))),
          None,
          Some(Ident("newTestRecord")),
          List(
            AbstractRecordField(
              Name(Some(Ident("f1"))), None,
              Qualid(List(Ident("A")))),
            AbstractRecordField(
              Name(Some(Ident("f2"))), None,
              Term_->(Qualid(List(Ident("B"))), Qualid(List(Ident("A"))))))),
        Definition(
          Ident("testRecordInstance"), None, None,
          UncurriedTermApplication(
            Qualid(List(Ident("newTestRecord"))),
            List(
              Argument(None, Qualid(List(Ident("nat")))),
              Argument(None, Qualid(List(Ident("bool")))),
              Argument(None, Number(7)),
              Argument(None,
                BetweenParenthesis(
                  Fun(Binders(List(
                    ExplicitBinderWithType(List(Name(Some(Ident("b")))), Qualid(List(Ident("bool")))))),
                    TermIf(Qualid(List(Ident("b"))), None, Number(3), Number(17)))))))))
    )
  }

  test("""Testing
       Definition testRecordFunction {A B} (R: @ TestRecord A B) := R.(f1).
    """) {
    CoqParser("""
              Definition testRecordFunction {A B} (R: @ TestRecord A B) := R.(f1).
              """) should parse(
      List(
        Definition(
          Ident("testRecordFunction"),
          Some(Binders(List(
            ImplicitBinder(List(Name(Some(Ident("A"))), Name(Some(Ident("B")))), None),
            ExplicitBinderWithType(
              List(Name(Some(Ident("R")))),
              ExplicitQualidApplication(Qualid(List(Ident("TestRecord"))), List(Qualid(List(Ident("A"))), Qualid(List(Ident("B"))))))))),
          None,
          SimpleProjection(Qualid(List(Ident("R"))), Qualid(List(Ident("f1"))))))
    )
  }

  test("""Testing
          Definition test1 := testRecordInstance.(f1).
    """) {
    CoqParser("""
          Definition test1 := testRecordInstance.(f1).
              """) should parse(
      List(
        Definition(
          Ident("test1"),
          None, None,
          SimpleProjection(Qualid(List(Ident("testRecordInstance"))), Qualid(List(Ident("f1"))))))
    )
  }

  test("""Testing
          Definition test2 := testRecordInstance.(f2) true.
    """) {
    CoqParser("""
          Definition test2 := testRecordInstance.(f2) true.
              """) should parse(
      List(
        Definition(
          Ident("test2"),
          None, None,
          UncurriedTermApplication(
            SimpleProjection(Qualid(List(Ident("testRecordInstance"))), Qualid(List(Ident("f2")))),
            List(Argument(None, Qualid(List(Ident("true"))))))))
    )
  }

  test("""Testing
          Definition test3 := testRecordFunction testRecordInstance.
    """) {
    CoqParser("""
          Definition test3 := testRecordFunction testRecordInstance.
              """) should parse(
      List(
        Definition(
          Ident("test3"),
          None, None,
          UncurriedTermApplication(
            Qualid(List(Ident("testRecordFunction"))),
            List(Argument(None, Qualid(List(Ident("testRecordInstance"))))))))
    )
  }

  test("""Testing
          Fixpoint size (t : Tree) : nat :=
           match t with
           | Leaf => 1
           | Node l r => (size l) + (size r)
           end.
          """) {
    CoqParser("""
          Fixpoint size (t : Tree) : nat :=
           match t with
           | Leaf => 1
           | Node l r => (size l) + (size r)
           end.
          """) should parse(
      List(
        Fixpoint(
          FixBody(Ident("size"),
            Binders(List(
              ExplicitBinderWithType(
                List(Name(Some(Ident("t")))),
                Qualid(List(Ident("Tree")))))),
            None,
            Some(Qualid(List(Ident("nat")))),
            Match(
              List(MatchItem(Qualid(List(Ident("t"))), None, None)),
              None,
              List(
                PatternEquation(List(MultPattern(List(
                  QualidPattern(Qualid(List(Ident("Leaf"))))))),
                  Number(1)),
                PatternEquation(List(MultPattern(List(
                  ConstructorPattern(
                    Qualid(List(Ident("Node"))),
                    List(
                      QualidPattern(Qualid(List(Ident("l")))),
                      QualidPattern(Qualid(List(Ident("r"))))))))),
                  InfixOperator(
                    BetweenParenthesis(
                      UncurriedTermApplication(
                        Qualid(List(Ident("size"))),
                        List(Argument(None, Qualid(List(Ident("l"))))))),
                    "+",
                    BetweenParenthesis(
                      UncurriedTermApplication(
                        Qualid(List(Ident("size"))),
                        List(Argument(None, Qualid(List(Ident("r"))))))))))))))
    )

  }

  test("""Testing
          Fixpoint size (t : Tree) { struct t } : nat :=
           match t with
           | Leaf => 1
           | Node l r => (size l) + (size r)
           end.
          """) {
    CoqParser("""
          Fixpoint size (t : Tree) { struct t } : nat :=
           match t with
           | Leaf => 1
           | Node l r => (size l) + (size r)
           end.
          """) should parse(
      List(
        Fixpoint(
          FixBody(Ident("size"),
            Binders(List(
              ExplicitBinderWithType(
                List(Name(Some(Ident("t")))),
                Qualid(List(Ident("Tree")))))),
            Some(FixAnnotation(Ident("t"))),
            Some(Qualid(List(Ident("nat")))),
            Match(
              List(MatchItem(Qualid(List(Ident("t"))), None, None)),
              None,
              List(
                PatternEquation(List(MultPattern(List(
                  QualidPattern(Qualid(List(Ident("Leaf"))))))),
                  Number(1)),
                PatternEquation(List(MultPattern(List(
                  ConstructorPattern(
                    Qualid(List(Ident("Node"))),
                    List(
                      QualidPattern(Qualid(List(Ident("l")))),
                      QualidPattern(Qualid(List(Ident("r"))))))))),
                  InfixOperator(
                    BetweenParenthesis(
                      UncurriedTermApplication(
                        Qualid(List(Ident("size"))),
                        List(Argument(None, Qualid(List(Ident("l"))))))),
                    "+",
                    BetweenParenthesis(
                      UncurriedTermApplication(
                        Qualid(List(Ident("size"))),
                        List(Argument(None, Qualid(List(Ident("r"))))))))))))))
    )

  }

  test("""Testing
          Fixpoint rightMost {A : Type} (t : BinTree) : A := match t with
           L x => x
          | N l r => rightMost r
          end.
          """) {
    CoqParser("""
          Fixpoint rightMost {A : Type} (t : BinTree) : A := match t with
           L x => x
          | N l r => rightMost r
          end.
          """) should parse(
      List(
        Fixpoint(
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

  test("""Testing
          Fixpoint rightMost {A : Type} (t : BinTree) := match t with
           L x => x
          | N l r => rightMost r
          end.
          """) {
    CoqParser("""
          Fixpoint rightMost {A : Type} (t : BinTree) := match t with
           L x => x
          | N l r => rightMost r
          end.
          """) should parse(
      List(
        Fixpoint(
          FixBody(Ident("rightMost"),
            Binders(List(
              ImplicitBinder(List(Name(Some(Ident("A")))), Some(Type)),
              ExplicitBinderWithType(List(Name(Some(Ident("t")))), Qualid(List(Ident("BinTree")))))),
            None,
            None,
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

  test("""Testing
          Fixpoint lenTailrec {A} (xs : list A) (n : nat) : nat :=
          match xs with
          | nil => n
          | _ :: ys => lenTailrec ys (1 + n)
          end.
          """) {
    CoqParser("""
          Fixpoint lenTailrec {A} (xs : list A) (n : nat) : nat :=
          match xs with
          | nil => n
          | _ :: ys => lenTailrec ys (1 + n)
          end.
          """) should parse(
      List(
        Fixpoint(
          FixBody(
            Ident("lenTailrec"),
            Binders(
              List(
                ImplicitBinder(List(Name(Some(Ident("A")))), None),
                ExplicitBinderWithType(
                  List(Name(Some(Ident("xs")))),
                  UncurriedTermApplication(Qualid(List(Ident("list"))), List(Argument(None, Qualid(List(Ident("A"))))))),
                ExplicitBinderWithType(
                  List(Name(Some(Ident("n")))),
                  Qualid(List(Ident("nat")))))),
            None,
            Some(Qualid(List(Ident("nat")))),
            Match(
              List(MatchItem(Qualid(List(Ident("xs"))), None, None)),
              None,
              List(
                PatternEquation(
                  List(MultPattern(List(QualidPattern(Qualid(List(Ident("nil"))))))),
                  Qualid(List(Ident("n")))),
                PatternEquation(
                  List(MultPattern(List(InfixPattern(UnderscorePattern, "::", QualidPattern(Qualid(List(Ident("ys")))))))),
                  UncurriedTermApplication(
                    Qualid(List(Ident("lenTailrec"))),
                    List(
                      Argument(None, Qualid(List(Ident("ys")))),
                      Argument(None, BetweenParenthesis(InfixOperator(Number(1), "+", Qualid(List(Ident("n"))))))))))))))
    )
  }

  test("""Testing
          Function lenTailrec {A} (xs : list A) (n : nat) { measure (fun xs => length(xs)) xs } : nat :=
          match xs with
          | nil => n
          | _ :: ys => lenTailrec ys (1 + n)
          end.
          Proof.
          intros.
          simpl.
          omega.
          Qed.
          """) {
    CoqParser("""
          Function lenTailrec {A} (xs : list A) (n : nat) { measure (fun xs => length(xs)) xs } : nat :=
          match xs with
          | nil => n
          | _ :: ys => lenTailrec ys (1 + n)
          end.
          Proof.
          intros.
          simpl.
          omega.
          Qed.
          """) should parse(
      List(
        FunctionDef(
          FunctionBody(
            Ident("lenTailrec"),
            Binders(
              List(
                ImplicitBinder(List(Name(Some(Ident("A")))), None),
                ExplicitBinderWithType(
                  List(Name(Some(Ident("xs")))),
                  UncurriedTermApplication(Qualid(List(Ident("list"))), List(Argument(None, Qualid(List(Ident("A"))))))),
                ExplicitBinderWithType(
                  List(Name(Some(Ident("n")))),
                  Qualid(List(Ident("nat")))))),
            FunAnnotation(
              Fun(
                Binders(List(ExplicitSimpleBinder(Name(Some(Ident("xs")))))),
                UncurriedTermApplication(
                  Qualid(List(Ident("length"))),
                  List(Argument(None, BetweenParenthesis(Qualid(List(Ident("xs")))))))),
              Ident("xs")),
            Some(Qualid(List(Ident("nat")))),
            Match(
              List(MatchItem(Qualid(List(Ident("xs"))), None, None)),
              None,
              List(
                PatternEquation(
                  List(MultPattern(List(QualidPattern(Qualid(List(Ident("nil"))))))),
                  Qualid(List(Ident("n")))),
                PatternEquation(
                  List(MultPattern(List(InfixPattern(UnderscorePattern, "::", QualidPattern(Qualid(List(Ident("ys")))))))),
                  UncurriedTermApplication(
                    Qualid(List(Ident("lenTailrec"))),
                    List(
                      Argument(None, Qualid(List(Ident("ys")))),
                      Argument(None, BetweenParenthesis(InfixOperator(Number(1), "+", Qualid(List(Ident("n"))))))))))))))
    )
  }

  test("""Testing
    Inductive Tree : Type :=
      Leaf : Tree
    | Node(l r : Tree): Tree.

    Fixpoint size (t: Tree) : nat :=
    match t with
      Leaf => 1
    | Node l r => 1 + (size l) + (size r)
    end.
    """) {
    CoqParser("""
              Inductive Tree : Type :=
                Leaf : Tree
              | Node(l r : Tree): Tree.

              Fixpoint size (t: Tree) : nat :=
              match t with
                Leaf => 1
              | Node l r => 1 + (size l) + (size r)
              end.
              """) should parse(
      List(
        Inductive(
          InductiveBody(Ident("Tree"), None, Some(Type),
            List(
              InductiveBodyItem(Ident("Leaf"),
                None,
                Some(Qualid(List(Ident("Tree"))))),
              InductiveBodyItem(Ident("Node"),
                Some(Binders(List(
                  ExplicitBinderWithType(
                    List(
                      Name(Some(Ident("l"))),
                      Name(Some(Ident("r")))),
                    Qualid(List(Ident("Tree"))))))),
                Some(Qualid(List(Ident("Tree")))))))),
        Fixpoint(
          FixBody(Ident("size"),
            Binders(List(
              ExplicitBinderWithType(
                List(Name(Some(Ident("t")))),
                Qualid(List(Ident("Tree")))))),
            None,
            Some(Qualid(List(Ident("nat")))),
            Match(
              List(MatchItem(Qualid(List(Ident("t"))), None, None)),
              None,
              List(
                PatternEquation(List(MultPattern(List(
                  QualidPattern(Qualid(List(Ident("Leaf"))))))),
                  Number(1)),
                PatternEquation(List(MultPattern(List(
                  ConstructorPattern(
                    Qualid(List(Ident("Node"))),
                    List(
                      QualidPattern(Qualid(List(Ident("l")))),
                      QualidPattern(Qualid(List(Ident("r"))))))))),
                  InfixOperator(
                    Number(1),
                    "+",
                    InfixOperator(
                      BetweenParenthesis(
                        UncurriedTermApplication(
                          Qualid(List(Ident("size"))),
                          List(Argument(None, Qualid(List(Ident("l"))))))),
                      "+",
                      BetweenParenthesis(
                        UncurriedTermApplication(
                          Qualid(List(Ident("size"))),
                          List(Argument(None, Qualid(List(Ident("r")))))))))))))))
    )
  }

  test("""Testing
        Definition matchOnTuple(tuple : nat * nat) := match tuple with
          (0, 0) => 5
        | (_, _) => 7
        end.
    """) {
    CoqParser("""
        Definition matchOnTuple(tuple : nat * nat) := match tuple with
          (0, 0) => 5
        | (_, _) => 7
        end.
              """) should parse(
      List(
        Definition(
          Ident("matchOnTuple"),
          Some(Binders(List(
            ExplicitBinderWithType(
              List(Name(Some(Ident("tuple")))),
              InfixOperator(Qualid(List(Ident("nat"))), "*", Qualid(List(Ident("nat")))))))),
          None,
          Match(
            List(MatchItem(Qualid(List(Ident("tuple"))), None, None)),
            None,
            List(
              PatternEquation(
                List(MultPattern(List(
                  ParenthesisOrPattern(List(
                    OrPattern(List(NumberPattern(Number(0)))),
                    OrPattern(List(NumberPattern(Number(0))))))))),
                Number(5)),
              PatternEquation(
                List(MultPattern(List(
                  ParenthesisOrPattern(List(
                    OrPattern(List(UnderscorePattern)),
                    OrPattern(List(UnderscorePattern))))))),
                Number(7))))))
    )
  }

  test("""Testing
        Definition matchOnTuple(x y : nat) := match x, y with
          0, 0 => 5
        | _, _ => 7
        end.
    """) {
    CoqParser("""
        Definition matchOnTuple(x y : nat) := match x, y with
          0, 0 => 5
        | _, _ => 7
        end.
              """) should parse(
      List(
        Definition(
          Ident("matchOnTuple"),
          Some(Binders(List(
            ExplicitBinderWithType(
              List(Name(Some(Ident("x"))), Name(Some(Ident("y")))),
              Qualid(List(Ident("nat"))))))),
          None,
          Match(
            List(
              MatchItem(Qualid(List(Ident("x"))), None, None),
              MatchItem(Qualid(List(Ident("y"))), None, None)),
            None,
            List(
              PatternEquation(
                List(MultPattern(List(
                  NumberPattern(Number(0)),
                  NumberPattern(Number(0))))),
                Number(5)),
              PatternEquation(
                List(MultPattern(List(
                  UnderscorePattern,
                  UnderscorePattern))),
                Number(7))))))
    )
  }

  test("""Testing
      Lemma testing (x : nat) : eq x x.
      Proof.
      auto.
      Qed.
    """) {
    CoqParser("""
      Lemma testing (x : nat) : eq x x.
      Proof.
      auto.
      Qed.
      """) should parse(
      List(
        Assertion(
          Lemma,
          Ident("testing"),
          Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat"))))))),
          UncurriedTermApplication(
            Qualid(List(Ident("eq"))),
            List(
              Argument(None, Qualid(List(Ident("x")))),
              Argument(None, Qualid(List(Ident("x")))))))))
  }

  test("""Testing
      Lemma testing (x : nat) : eq x x.
      Proof.
      auto.
      Defined.
    """) {
    CoqParser("""
      Lemma testing (x : nat) : eq x x.
      Proof.
      auto.
      Defined.
      """) should parse(
      List(
        Assertion(
          Lemma,
          Ident("testing"),
          Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat"))))))),
          UncurriedTermApplication(
            Qualid(List(Ident("eq"))),
            List(
              Argument(None, Qualid(List(Ident("x")))),
              Argument(None, Qualid(List(Ident("x")))))))))
  }

  test("""Testing
    Lemma testing (x : nat) : eq x x.
    Proof.
    Admitted.
    """) {
    CoqParser("""
      Lemma testing (x : nat) : eq x x.
      Proof.
      Admitted.
      """) should parse(
      List(
        Assertion(
          Lemma,
          Ident("testing"),
          Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat"))))))),
          UncurriedTermApplication(
            Qualid(List(Ident("eq"))),
            List(
              Argument(None, Qualid(List(Ident("x")))),
              Argument(None, Qualid(List(Ident("x")))))))))
  }

  test("""Testing
      Lemma testing (x : nat) : eq x x.
      Proof.
      intros.
      auto.
      Qed.
    """) {
    CoqParser("""
      Lemma testing (x : nat) : eq x x.
      Proof.
      intros.
      auto.
      Qed.
      """) should parse(
      List(
        Assertion(
          Lemma,
          Ident("testing"),
          Some(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat"))))))),
          UncurriedTermApplication(
            Qualid(List(Ident("eq"))),
            List(
              Argument(None, Qualid(List(Ident("x")))),
              Argument(None, Qualid(List(Ident("x")))))))))
  }

  test("""Testing
    Theorem testing: forall (x : nat), eq x x.
    Proof.
    intros.
    auto.
    Qed.
    """) {
    CoqParser("""
      Theorem testing: forall (x : nat), eq x x.
      Proof.
      intros.
      auto.
      Qed.
      """) should parse(
      List(
        Assertion(
          Theorem,
          Ident("testing"),
          None,
          ForAll(
            Binders(
              List(
                ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat")))))),
            UncurriedTermApplication(
              Qualid(List(Ident("eq"))),
              List(
                Argument(None, Qualid(List(Ident("x")))),
                Argument(None, Qualid(List(Ident("x")))))))))
    )
  }

  test("""Testing
    Lemma testing: forall (x : nat), eq x x.
    Proof.
    intros.
    auto.
    Qed.
    """) {
    CoqParser("""
      Lemma testing: forall (x : nat), eq x x.
      Proof.
      intros.
      auto.
      Qed.
      """) should parse(
      List(
        Assertion(
          Lemma,
          Ident("testing"),
          None,
          ForAll(
            Binders(
              List(
                ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat")))))),
            UncurriedTermApplication(
              Qualid(List(Ident("eq"))),
              List(
                Argument(None, Qualid(List(Ident("x")))),
                Argument(None, Qualid(List(Ident("x")))))))))
    )
  }

  test("""Testing
    Remark testing: forall (x : nat), eq x x.
    Proof.
    intros.
    auto.
    Qed.
    """) {
    CoqParser("""
      Remark testing: forall (x : nat), eq x x.
      Proof.
      intros.
      auto.
      Qed.
      """) should parse(
      List(
        Assertion(
          Remark,
          Ident("testing"),
          None,
          ForAll(
            Binders(
              List(
                ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat")))))),
            UncurriedTermApplication(
              Qualid(List(Ident("eq"))),
              List(
                Argument(None, Qualid(List(Ident("x")))),
                Argument(None, Qualid(List(Ident("x")))))))))
    )
  }

  test("""Testing
    Fact testing: forall (x : nat), eq x x.
    Proof.
    intros.
    auto.
    Qed.
    """) {
    CoqParser("""
      Fact testing: forall (x : nat), eq x x.
      Proof.
      intros.
      auto.
      Qed.
      """) should parse(
      List(
        Assertion(
          Fact,
          Ident("testing"),
          None,
          ForAll(
            Binders(
              List(
                ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat")))))),
            UncurriedTermApplication(
              Qualid(List(Ident("eq"))),
              List(
                Argument(None, Qualid(List(Ident("x")))),
                Argument(None, Qualid(List(Ident("x")))))))))
    )
  }

  test("""Testing
    Corollary testing: forall (x : nat), eq x x.
    Proof.
    intros.
    auto.
    Qed.
    """) {
    CoqParser("""
      Corollary testing: forall (x : nat), eq x x.
      Proof.
      intros.
      auto.
      Qed.
      """) should parse(
      List(
        Assertion(
          Corollary,
          Ident("testing"),
          None,
          ForAll(
            Binders(
              List(
                ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat")))))),
            UncurriedTermApplication(
              Qualid(List(Ident("eq"))),
              List(
                Argument(None, Qualid(List(Ident("x")))),
                Argument(None, Qualid(List(Ident("x")))))))))
    )
  }

  test("""Testing
    Proposition testing: forall (x : nat), eq x x.
    Proof.
    intros.
    auto.
    Qed.
    """) {
    CoqParser("""
      Proposition testing: forall (x : nat), eq x x.
      Proof.
      intros.
      auto.
      Qed.
      """) should parse(
      List(
        Assertion(
          Proposition,
          Ident("testing"),
          None,
          ForAll(
            Binders(
              List(
                ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat")))))),
            UncurriedTermApplication(
              Qualid(List(Ident("eq"))),
              List(
                Argument(None, Qualid(List(Ident("x")))),
                Argument(None, Qualid(List(Ident("x")))))))))
    )
  }

  test("""Testing
    Definition testing: forall (x : nat), eq x x.
    Proof.
    intros.
    auto.
    Qed.
    """) {
    CoqParser("""
      Definition testing: forall (x : nat), eq x x.
      Proof.
      intros.
      auto.
      Qed.
      """) should parse(
      List(
        Assertion(
          DefinitionAssertionKeyword,
          Ident("testing"),
          None,
          ForAll(
            Binders(
              List(
                ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat")))))),
            UncurriedTermApplication(
              Qualid(List(Ident("eq"))),
              List(
                Argument(None, Qualid(List(Ident("x")))),
                Argument(None, Qualid(List(Ident("x")))))))))
    )
  }

  test("""Testing
    Example testing: forall (x : nat), eq x x.
    Proof.
    intros.
    auto.
    Qed.
    """) {
    CoqParser("""
      Example testing: forall (x : nat), eq x x.
      Proof.
      intros.
      auto.
      Qed.
      """) should parse(
      List(
        Assertion(
          Example,
          Ident("testing"),
          None,
          ForAll(
            Binders(
              List(
                ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat")))))),
            UncurriedTermApplication(
              Qualid(List(Ident("eq"))),
              List(
                Argument(None, Qualid(List(Ident("x")))),
                Argument(None, Qualid(List(Ident("x")))))))))
    )
  }

  // TODO (Joseph Bakouny): It should be noted that a binder with a type but no parenthesis is not parsed correctly.
  ignore("""Testing
    Lemma testing: forall x : nat, eq x x.
    Proof.
    intros.
    auto.
    Qed.
    """) {
    CoqParser("""
      Lemma testing: forall x : nat, eq x x.
      Proof.
      intros.
      auto.
      Qed.
      """) should parse(
      List(
        Assertion(
          Lemma,
          Ident("testing"),
          None,
          ForAll(
            Binders(
              List(
                ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat")))))),
            UncurriedTermApplication(
              Qualid(List(Ident("eq"))),
              List(
                Argument(None, Qualid(List(Ident("x")))),
                Argument(None, Qualid(List(Ident("x")))))))))
    )
  }

}
