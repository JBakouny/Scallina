package scala.of.coq.parsercombinators

import scala.of.coq.parsercombinators.compiler.ScalaOfCoq
import scala.of.coq.parsercombinators.parser.CoqParser

import org.scalatest.Finders
import org.scalatest.FunSuite
import org.scalatest.Matchers.convertToAnyShouldWrapper

import CustomMatchers.generateScalaCode

import scala.of.coq.parsercombinators.compiler.Currify

class ScalaOfCoqCurrifiedTest extends FunSuite {

  implicit val curryingStrategy = Currify

  test("""Testing Scala conversion of
        Definition curryAdd : Z -> Z -> Z :=
          fun (x y : Z) => x.
    """) {
    CoqParser("""
        Definition curryAdd : Z -> Z -> Z :=
          fun (x y : Z) => x.
      """) should generateScalaCode("""
      "def curryAdd: BigInt => BigInt => BigInt =
      "  (x: BigInt) => (y: BigInt) => x
      """)
  }

  test("""Testing Scala conversion of
    Definition testSimpleLetWithBinders (x: nat) : nat :=
      let f (a b : nat) := a * b in f 7 3.
       """) {
    CoqParser("""
      Definition testSimpleLetWithBinders (x: nat) : nat :=
        let f (a b : nat) := a * b in f 7 3.
      """) should generateScalaCode("""
      "def testSimpleLetWithBinders(x: Nat): Nat = {
      "  val f = (a: Nat) => (b: Nat) => a * b
      "  f(7)(3)
      "}
      """)
  }

  test("""Testing Scala conversion of
          Require Import Omega.

          Inductive Tree (A: Type) :=
            Leaf(value: A)
          | Node(l r : Tree A).

          Arguments Leaf {A} _.
          Arguments Node {A} _ _.

          Fixpoint size {A} (t: Tree A) : nat :=
          match t with
            Leaf _ => 1
          | Node l r => 1 + (size l) + (size r)
          end.

          Lemma size_left: forall A (l r: Tree A), size (Node l r) > size l.
          Proof.
            intros; induction l; simpl; omega.
          Qed.

          Fixpoint map {A B} (t: Tree A) (f: A -> B) : Tree B :=
          match t with
            Leaf a => Leaf (f a)
          | Node l r => Node (map l f) (map r f)
          end.
       """) {
    CoqParser("""
          Require Import Omega.

          Inductive Tree (A: Type) :=
            Leaf(value: A)
          | Node(l r : Tree A).

          Arguments Leaf {A} _.
          Arguments Node {A} _ _.

          Fixpoint size {A} (t: Tree A) : nat :=
          match t with
            Leaf _ => 1
          | Node l r => 1 + (size l) + (size r)
          end.

          Lemma size_left: forall A (l r: Tree A), size (Node l r) > size l.
          Proof.
            intros; induction l; simpl; omega.
          Qed.

          Fixpoint map {A B} (t: Tree A) (f: A -> B) : Tree B :=
          match t with
            Leaf a => Leaf (f a)
          | Node l r => Node (map l f) (map r f)
          end.
      """) should generateScalaCode("""
        "sealed abstract class Tree[A]
        "case class Leaf[A](value: A) extends Tree[A]
        "case class Node[A](l: Tree[A], r: Tree[A]) extends Tree[A]
        "object Node {
        "  def apply[A] =
        "    (l: Tree[A]) => (r: Tree[A]) => new Node(l, r)
        "}
        "def size[A](t: Tree[A]): Nat =
        "  t match {
        "    case Leaf(_)    => 1
        "    case Node(l, r) => 1 + (size(l) + size(r))
        "  }
        "def map[A, B](t: Tree[A])(f: A => B): Tree[B] =
        "  t match {
        "    case Leaf(a)    => Leaf(f(a))
        "    case Node(l, r) => Node(map(l)(f))(map(r)(f))
        "  }
        """)
  }

  test("""Testing Scala conversion of
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
      """) should generateScalaCode("""
      "trait Queue {
      "  type T
      "  def empty: T
      "  def push: Nat => T => T
      "  def pop: T => Option[(Nat, T)]
      "}
      "def Build_Queue[T](empty: T)(push: Nat => T => T)(pop: T => Option[(Nat, T)]): Queue = {
      "  type Queue_T = T
      "  def Queue_empty = empty
      "  def Queue_push = push
      "  def Queue_pop = pop
      "  new Queue {
      "    type T = Queue_T
      "    def empty: T = Queue_empty
      "    def push: Nat => T => T = Queue_push
      "    def pop: T => Option[(Nat, T)] = Queue_pop
      "  }
      "}
      """)
  }

  test("""Testing Scala conversion of
          Record Queue := newQueue {
            T : Type;
            empty : T;
            push (x : nat) (q : T) : T;
            pop (q: T) : option (nat * T)
          }.
       """) {
    CoqParser("""
      Record Queue := newQueue {
        T : Type;
        empty : T;
        push (x : nat) (q : T) : T;
        pop (q: T) : option (nat * T)
      }.
      """) should generateScalaCode("""
      "trait Queue {
      "  type T
      "  def empty: T
      "  def push: Nat => T => T
      "  def pop: T => Option[(Nat, T)]
      "}
      "def newQueue[T](empty: T)(push: Nat => T => T)(pop: T => Option[(Nat, T)]): Queue = {
      "  type Queue_T = T
      "  def Queue_empty = empty
      "  def Queue_push = push
      "  def Queue_pop = pop
      "  new Queue {
      "    type T = Queue_T
      "    def empty: T = Queue_empty
      "    def push: Nat => T => T = Queue_push
      "    def pop: T => Option[(Nat, T)] = Queue_pop
      "  }
      "}
      """)
  }

  test("""Testing Scala conversion of
          Fixpoint insertElems (Q: Queue) (q: Q.(T)) (n: nat) : Q.(T) :=
          match n with
            0 => q
          | S m => Q.(push) n (insertElems Q q m)
          end.

          Definition createQueue (Q: Queue) (n: nat) : Q.(T) := insertElems Q Q.(empty) n.

          Definition createListQueue(n: nat) := createQueue ListQueue n.

          Definition createDListQueue(n: nat) := createQueue DListQueue n.
       """) {
    CoqParser("""
          Fixpoint insertElems (Q: Queue) (q: Q.(T)) (n: nat) : Q.(T) :=
          match n with
            0 => q
          | S m => Q.(push) n (insertElems Q q m)
          end.

          Definition createQueue (Q: Queue) (n: nat) : Q.(T) := insertElems Q Q.(empty) n.

          Definition createListQueue(n: nat) := createQueue ListQueue n.

          Definition createDListQueue(n: nat) := createQueue DListQueue n.
      """) should generateScalaCode("""
      "def insertElems(Q: Queue)(q: Q.T)(n: Nat): Q.T =
      "  n match {
      "    case Zero => q
      "    case S(m) => Q.push(n)(insertElems(Q)(q)(m))
      "  }
      "def createQueue(Q: Queue)(n: Nat): Q.T = insertElems(Q)(Q.empty)(n)
      "def createListQueue(n: Nat) = createQueue(ListQueue)(n)
      "def createDListQueue(n: Nat) = createQueue(DListQueue)(n)
      """)
  }

  test("""Testing Scala conversion of
        Record TestRecord :=
        {
          testAbstractField : nat;
          testConcreteField : nat := testAbstractField + 3;
          testFunction (x : nat) : nat := x + 7;
          testAnonFun : nat -> nat := fun (x : nat) => x + 3
        }.
       """) {
    CoqParser("""
      Record TestRecord :=
      {
        testAbstractField : nat;
        testConcreteField : nat := testAbstractField + 3;
        testFunction (x : nat) : nat := x + 7;
        testAnonFun : nat -> nat := fun (x : nat) => x + 3
      }.
      """) should generateScalaCode("""
      "trait TestRecord {
      "  def testAbstractField: Nat
      "  def testConcreteField: Nat = testAbstractField + 3
      "  def testFunction: Nat => Nat = (x: Nat) => x + 7
      "  def testAnonFun: Nat => Nat = (x: Nat) => x + 3
      "}
      "def Build_TestRecord(testAbstractField: Nat): TestRecord = {
      "  def TestRecord_testAbstractField = testAbstractField
      "  new TestRecord {
      "    def testAbstractField: Nat = TestRecord_testAbstractField
      "  }
      "}
      """)
  }

  test("""Testing Scala conversion of
        Record TestRecord {A} :=
        {
          testAbstractField : A;
          testConcreteField : A := testAbstractField;
          testFunction (x : A) : A := x;
          testAnonFun : A -> A := fun (x : A) => x
        }.
       """) {
    CoqParser("""
      Record TestRecord {A} :=
      {
        testAbstractField : A;
        testConcreteField : A := testAbstractField;
        testFunction (x : A) : A := x;
        testAnonFun : A -> A := fun (x : A) => x
      }.
      """) should generateScalaCode("""
      "trait TestRecord[A] {
      "  def testAbstractField: A
      "  def testConcreteField: A = testAbstractField
      "  def testFunction: A => A = (x: A) => x
      "  def testAnonFun: A => A = (x: A) => x
      "}
      "def Build_TestRecord[A](testAbstractField: A): TestRecord[A] = {
      "  def TestRecord_testAbstractField = testAbstractField
      "  new TestRecord[A] {
      "    def testAbstractField: A = TestRecord_testAbstractField
      "  }
      "}
      """)
  }

  test("""Testing Scala conversion of
          Record TestRecord {A B} :=
          newTestRecord {
            f1 : A;
            f2 : B -> A
          }.
       """) {
    CoqParser("""
      Record TestRecord {A B} :=
      newTestRecord {
        f1 : A;
        f2 : B -> A
      }.
      """) should generateScalaCode("""
      "trait TestRecord[A, B] {
      "  def f1: A
      "  def f2: B => A
      "}
      "def newTestRecord[A, B](f1: A)(f2: B => A): TestRecord[A, B] = {
      "  def TestRecord_f1 = f1
      "  def TestRecord_f2 = f2
      "  new TestRecord[A, B] {
      "    def f1: A = TestRecord_f1
      "    def f2: B => A = TestRecord_f2
      "  }
      "}
      """)
  }

  test("""Testing Scala conversion of
      Definition testRecordFunction {A B} (R: @ TestRecord A B) := R.(f1).
      Definition test1 := testRecordInstance.(f1).
      Definition test2 := testRecordInstance.(f2) true.
      Definition test3 := testRecordFunction testRecordInstance.
       """) {
    CoqParser("""
      Definition testRecordFunction {A B} (R: @ TestRecord A B) := R.(f1).
      Definition test1 := testRecordInstance.(f1).
      Definition test2 := testRecordInstance.(f2) true.
      Definition test3 := testRecordFunction testRecordInstance.
      """) should generateScalaCode("""
      "def testRecordFunction[A, B](R: TestRecord[A, B]) = R.f1
      "def test1 = testRecordInstance.f1
      "def test2 = testRecordInstance.f2(true)
      "def test3 = testRecordFunction(testRecordInstance)
      """)
  }

  // TODO(Joseph Bakouny): Consider implementing the support of concrete type field replacements in the constructor's arguments.
  ignore("""Testing Scala conversion of
          Record ComplicatedRecord :=
          newComplicatedRecord {
            B : Type := nat;
            T (A : Type) : Type := list A;
            f (x: T B) : T B
          }.
       """) {
    CoqParser("""
      Record ComplicatedRecord :=
      newComplicatedRecord {
        B : Type := nat;
        T (A : Type) : Type := list A;
        f (x: T B) : T B
      }.
      """) should generateScalaCode("""
      "trait ComplicatedRecord {
      "  type B = Nat
      "  type T[A] = List[A]
      "  def f: T[B] => T[B]
      "}
      "def newComplicatedRecord(f: List[Nat] => List[Nat]): ComplicatedRecord = {
      "  def ComplicatedRecord_f = f
      "  new ComplicatedRecord {
      "    def f: T[B] => T[B] = ComplicatedRecord_f
      "  }
      "}
      """)
  }

  test("""Testing Scala conversion of
          Definition prepend (a : nat) (l: list nat) := a :: l.
          Definition test := prepend 3 (record.(f) (7 :: nil)).
       """) {
    CoqParser("""
        Definition prepend (a : nat) (l: list nat) := a :: l.
        Definition test := prepend 3 (record.(f) (7 :: nil)).
      """) should generateScalaCode("""
      "def prepend(a: Nat)(l: List[Nat]) = a :: l
      "def test = prepend(3)(record.f(7 :: Nil))
      """)
  }

  test("""Testing Scala conversion of
          Require Import Coq.Lists.List.

          Record Queue :=
          {
            T : Type;
            push : nat -> T -> T;
            pop : T -> option (nat * T);
            empty : T
          }.

          Arguments Build_Queue {T} _ _ _.

          Definition ListQueue := Build_Queue
            (fun (x : nat) (l : list nat) => x :: l)
            (fun l =>
              match rev l with
                | nil => None
                | hd :: tl => Some (hd, rev tl) end)
            nil
          .

          Definition DListQueue := Build_Queue
            (fun (x : nat) (l : (list nat) * (list nat)) =>
              let (back, front) := l in
              (x :: back,front))
            (fun l =>
              let (back, front) := l in
              match front with
                | nil =>
                   match rev back with
                      | nil => None
                      | hd :: tl => Some (hd, (nil, tl))
                   end
                | hd :: tl => Some (hd, (back, tl))
              end)
            (nil, nil)
          .
       """) {
    CoqParser("""
          Require Import Coq.Lists.List.

          Record Queue :=
          {
            T : Type;
            push : nat -> T -> T;
            pop : T -> option (nat * T);
            empty : T
          }.

          Arguments Build_Queue {T} _ _ _.

          Definition ListQueue := Build_Queue
            (fun (x : nat) (l : list nat) => x :: l)
            (fun l =>
              match rev l with
                | nil => None
                | hd :: tl => Some (hd, rev tl) end)
            nil
          .

          Definition DListQueue := Build_Queue
            (fun (x : nat) (l : (list nat) * (list nat)) =>
              let (back, front) := l in
              (x :: back,front))
            (fun l =>
              let (back, front) := l in
              match front with
                | nil =>
                   match rev back with
                      | nil => None
                      | hd :: tl => Some (hd, (nil, tl))
                   end
                | hd :: tl => Some (hd, (back, tl))
              end)
            (nil, nil)
          .
      """) should generateScalaCode("""
      "trait Queue {
      "  type T
      "  def push: Nat => T => T
      "  def pop: T => Option[(Nat, T)]
      "  def empty: T
      "}
      "def Build_Queue[T](push: Nat => T => T)(pop: T => Option[(Nat, T)])(empty: T): Queue = {
      "  type Queue_T = T
      "  def Queue_push = push
      "  def Queue_pop = pop
      "  def Queue_empty = empty
      "  new Queue {
      "    type T = Queue_T
      "    def push: Nat => T => T = Queue_push
      "    def pop: T => Option[(Nat, T)] = Queue_pop
      "    def empty: T = Queue_empty
      "  }
      "}
      "def ListQueue = Build_Queue((x: Nat) => (l: List[Nat]) => x :: l)(l => rev(l) match {
      "  case Nil      => None
      "  case hd :: tl => Some((hd, rev(tl)))
      "})(Nil)
      "def DListQueue = Build_Queue((x: Nat) => { (l: (List[Nat], List[Nat])) =>
      "  val (back, front) = l
      "  (x :: back, front)
      "})({ l =>
      "  val (back, front) = l
      "  front match {
      "    case Nil => rev(back) match {
      "      case Nil      => None
      "      case hd :: tl => Some((hd, (Nil, tl)))
      "    }
      "    case hd :: tl => Some((hd, (back, tl)))
      "  }
      "})((Nil, Nil))
      """)
  }
}
