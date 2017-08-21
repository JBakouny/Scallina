package scala.of.coq.parsercombinators

import scala.of.coq.parsercombinators.compiler.ScalaOfCoq
import scala.of.coq.parsercombinators.parser.CoqParser

import org.scalatest.Finders
import org.scalatest.FunSuite
import org.scalatest.Matchers.convertToAnyShouldWrapper

import CustomMatchers.generateScalaCode

class ScallinaScalaOfCoqTest extends FunSuite {

  def coqParserShouldFailToGenerateScalaCodeFor(coqCode: String) {
    val parseResult = CoqParser(coqCode)
    assertThrows[IllegalStateException] {
      parseResult.map(ScalaOfCoq.toScalaCode(_))
    }
  }

  test("""Testing that explicit Type parameters are not supported if the return type is not Type
      Definition illegalFunction (x: Type) := x -> x.
       """) {
    coqParserShouldFailToGenerateScalaCodeFor("""
        Definition illegalFunction (x: Type) := x -> x.
        """)
  }

  test("""Testing Scala conversion of "Definition legalFunction (x: Type) : Type := x -> x." """) {
    CoqParser("Definition legalFunction (x: Type) : Type := x -> x.") should
      generateScalaCode("type legalFunction[x] = x => x")
  }

  test("""Testing Scala conversion of "Definition newTypeAlias : Type := nat -> nat." """) {
    CoqParser("Definition newTypeAlias : Type := nat -> nat.") should
      generateScalaCode("type newTypeAlias = Nat => Nat")
  }

  test("""Testing that explicit Prop parameters are not supported
      Definition illegalFunction (x: Prop) := 3.
       """) {
    coqParserShouldFailToGenerateScalaCodeFor("""
        Definition illegalFunction (x: Prop) := 3.
        """)
  }

  test("""Testing that explicit Set parameters are not supported
      Definition illegalFunction (x: Set) := 3.
       """) {
    coqParserShouldFailToGenerateScalaCodeFor("""
        Definition illegalFunction (x: Set) := 3.
        """)
  }

  test("""Testing that implicit anonymous function parameters are not supported
        Definition illegalDef :=
          fun {A} (x : A) => x.
       """) {
    coqParserShouldFailToGenerateScalaCodeFor("""
        Definition illegalDef :=
          fun {A} (x : A) => x.
        """)
  }

  test("""Testing Scala conversion of "Require Import Coq.Arith.PeanoNat." """) {
    CoqParser("Require Import Coq.Arith.PeanoNat.") should
      generateScalaCode("")
  }

  test("""Testing Scala conversion of "Local Open Scope Z_scope." """) {
    CoqParser("Local Open Scope Z_scope.") should
      generateScalaCode("")
  }

  test("""Testing Scala conversion of "Open Scope Z_scope." """) {
    CoqParser("Open Scope Z_scope.") should
      generateScalaCode("")
  }

  test("""Testing Scala conversion of "Arguments Node {A} _ _." """) {
    CoqParser("Arguments Node {A} _ _.") should
      generateScalaCode("")
  }

  test("""Testing Scala conversion of "Definition f(a : A) := 3." """) {
    CoqParser("Definition f(a : A) := 3.") should
      generateScalaCode("def f(a: A) = 3")
  }

  test("""Testing Scala conversion of "Definition f(l : list bool) := 3." """) {
    CoqParser("Definition f(l : list bool) := 3.") should
      generateScalaCode("def f(l: List[Boolean]) = 3")
  }

  test("""Testing Scala conversion of "Definition right {A : Type} (l r : A) := r." """) {
    CoqParser("Definition right {A : Type} (l r : A) := r.") should
      generateScalaCode("def right[A](l: A, r: A) = r")
  }

  test("""Testing Scala conversion of
      Definition testPrimitiveBooleans := true.
       """) {
    CoqParser("Definition testPrimitiveBooleans := true.") should
      generateScalaCode("def testPrimitiveBooleans = true")
  }

  // TODO(Joseph Bakouny): Consider removing the support of Prop value conversions
  test("""Testing Scala conversion of
      Definition testPrimitiveBooleans := True.
       """) {
    CoqParser("Definition testPrimitiveBooleans := True.") should
      generateScalaCode("def testPrimitiveBooleans = true")
  }

  test("""Testing Scala conversion of
      Definition testPrimitiveBooleans := false.
       """) {
    CoqParser("Definition testPrimitiveBooleans := false.") should
      generateScalaCode("def testPrimitiveBooleans = false")
  }

  // TODO(Joseph Bakouny): Consider removing the support of Prop value conversions
  test("""Testing Scala conversion of
      Definition testPrimitiveBooleans := False.
       """) {
    CoqParser("Definition testPrimitiveBooleans := False.") should
      generateScalaCode("def testPrimitiveBooleans = false")
  }

  test("""Testing Scala conversion of
        Definition empty : Z -> Z :=
          fun x => 0.
    """) {
    CoqParser("""
        Definition empty : Z -> Z :=
          fun x => 0.
      """) should generateScalaCode("""
      "def empty: BigInt => BigInt =
      "  x => 0
      """)
  }

  test("""Testing Scala conversion of
        Definition id : Z -> Z :=
          fun x => x.
    """) {
    CoqParser("""
        Definition id : Z -> Z :=
          fun x => x.
      """) should generateScalaCode("""
      "def id: BigInt => BigInt =
      "   x => x
      """)
  }

  test("""Testing Scala conversion of
        Definition add : Z -> Z -> Z :=
          fun x => fun y => x + y.
    """) {
    CoqParser("""
        Definition add : Z -> Z -> Z :=
          fun x => fun y => x + y.
      """) should generateScalaCode("""
      "def add: BigInt => BigInt => BigInt =
      "  x => y => x + y
      """)
  }

  // NOTE: All Coq lambdas are transformed into currified Scala anonymous functions
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

  test("""Testing Scala conversion of "Definition add(x y : nat) : nat := x + y." """) {
    CoqParser("""
          Definition add(x y : nat) : nat := x + y.
      """) should generateScalaCode("def add(x: Nat, y: Nat): Nat = x + y")
  }

  test("""Testing Scala conversion of "Definition add(x y z : nat) : nat := x + y." """) {
    CoqParser("""
          Definition add(x y z : nat) : nat := x + y + z.
      """) should generateScalaCode("def add(x: Nat, y: Nat, z: Nat): Nat = x + (y + z)")
  }

  test("""Testing Scala conversion of "Definition addTen(n : nat) : nat := add n 10." """) {
    CoqParser("Definition addTen(n : nat) : nat := add n 10.") should
      generateScalaCode("def addTen(n: Nat): Nat = add(n, 10)")
  }

  test("""Testing Scala conversion of "Definition addTen(n : nat) : nat := (add n 10)." """) {
    CoqParser("""
          Definition addTen(n : nat) : nat := (add n 10).
      """) should generateScalaCode("def addTen(n: Nat): Nat = add(n, 10)")
  }

  test("""Testing Scala conversion of
        Definition amortizedQueue (front rear: List) : AbsQueue :=
          if (size rear) <=? (size front) then
            Queue front rear
          else
            Queue (concat front (reverse rear)) Nil.
       """) {
    CoqParser("""
        Definition amortizedQueue (front rear: List) : AbsQueue :=
          if (size rear) <=? (size front) then
            Queue front rear
          else
            Queue (concat front (reverse rear)) Nil.
      """) should generateScalaCode("""
      "def amortizedQueue(front: List, rear: List): AbsQueue =
      "  if (size(rear) <= size(front)) Queue(front, rear)
      "  else Queue(concat(front, reverse(rear)), Nil)
      """)
  }

  test("""Testing Scala conversion of
        Definition testOp : nat :=
          if 3 <? 7 then
            1
          else
            2.
       """) {
    CoqParser("""
        Definition testOp : nat :=
          if 3 <? 7 then
            1
          else
            2.
      """) should generateScalaCode("""
      "def testOp: Nat =
      "  if (3 < 7) 1
      "  else 2
      """)
  }

  test("""Testing Scala conversion of
        Definition testOp : nat :=
          if 3 =? 7 then
            1
          else
            2.
       """) {
    CoqParser("""
        Definition testOp : nat :=
          if 3 =? 7 then
            1
          else
            2.
      """) should generateScalaCode("""
      "def testOp: Nat =
      "  if (3 == 7) 1
      "  else 2
      """)
  }

  test("""Testing Scala conversion of
        Inductive Tree:=
          Leaf
        | Node(l r : Tree).
       """) {
    CoqParser("""
         Inductive Tree:=
          Leaf
        | Node(l r : Tree).
      """) should generateScalaCode("""
        "sealed abstract class Tree
        "case object Leaf extends Tree
        "case class Node(l: Tree, r: Tree) extends Tree
        """)
  }

  test("""Testing Scala conversion of
      Fixpoint lenTailrec {A} (xs : list A) (n : Z) : Z :=
      match xs with
      | nil => n
      | cons _ ys => lenTailrec ys (1 + n)
      end.
       """) {
    CoqParser("""
      Fixpoint lenTailrec {A} (xs : list A) (n : Z) : Z :=
      match xs with
      | nil => n
      | cons _ ys => lenTailrec ys (1 + n)
      end.
      """) should generateScalaCode("""
      "def lenTailrec[A](xs: List[A], n: BigInt): BigInt =
      "  xs match {
      "   case Nil => n
      "   case Cons(_, ys) => lenTailrec(ys, 1 + n)
      " }
      """)
  }

  test("""Testing Scala conversion of
      Fixpoint lenTailrec {A} (xs : list A) (n : nat) : nat :=
      match xs with
      | nil => n
      | cons _ ys => lenTailrec ys (1 + n)
      end.
       """) {
    CoqParser("""
      Fixpoint lenTailrec {A} (xs : list A) (n : nat) : nat :=
      match xs with
      | nil => n
      | cons _ ys => lenTailrec ys (1 + n)
      end.
      """) should generateScalaCode("""
      "def lenTailrec[A](xs: List[A], n: Nat): Nat =
      "  xs match {
      "   case Nil => n
      "   case Cons(_, ys) => lenTailrec(ys, 1 + n)
      " }
      """)
  }

  test("""Testing Scala conversion of
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
      """) should generateScalaCode("""
      "def lenTailrec[A](xs: List[A], n: Nat): Nat =
      "  xs match {
      "   case Nil => n
      "   case _ :: ys => lenTailrec(ys, 1 + n)
      " }
      """)
  }

  test("""Testing Scala conversion of
      Definition testSimpleLet (x: nat) : nat :=
        let y := 2 * x in 7 * y.
       """) {
    CoqParser("""
      Definition testSimpleLet (x: nat) : nat :=
        let y := 2 * x in 7 * y.
      """) should generateScalaCode("""
      "def testSimpleLet(x: Nat): Nat = {
      " val y = 2 * x
      " 7 * y
      "}
      """)
  }

  test("""Testing Scala conversion of
      Definition testSimpleLetWithBinders (x: nat) : nat :=
        let f (a : nat) := 3 * a in 7 * (f x).
       """) {
    CoqParser("""
      Definition testSimpleLetWithBinders (x: nat) : nat :=
        let f (a : nat) := 3 * a in 7 * (f x).
      """) should generateScalaCode("""
      "def testSimpleLetWithBinders(x: Nat): Nat = {
      " val f = (a: Nat) => 3 * a
      " 7 * f(x)
      "}
      """)
  }

  /*
   * TODO(Joseph Bakouny): Consider changing the default behavior of
   * the generated Scala function applications from uncurrified applications (and definitions) to
   * currified applications and definitions.
   * In fact, this best mimics Coq and OCaml functions which are all currified one argument functions.
   *
   * Also implement a command line option to switch back to uncurrified definitions.
   */
  ignore("""Testing Scala conversion of
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
        Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
        match l with
        |  nil => (x, nil)
        |  h::t => if x <=? h
                       then let (j, l2) := select x t in (j, h::l2)
                       else let (j, l2) := select h t in (j, x::l2)
        end.
       """) {
    CoqParser("""
        Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
        match l with
        |  nil => (x, nil)
        |  h::t => if x <=? h
                       then let (j, l2) := select x t in (j, h::l2)
                       else let (j, l2) := select h t in (j, x::l2)
        end.
      """) should generateScalaCode("""
      "def select(x: Nat, l: List[Nat]): (Nat, List[Nat]) =
      "  l match {
      "    case Nil => (x, Nil)
      "    case h :: t => if (x <= h) {
      "      val (j, l2) = select(x, t)
      "      (j, h :: l2)
      "    }
      "    else {
      "      val (j, l2) = select(h, t)
      "      (j, x :: l2)
      "    }
      "  }
      """)
  }

  test("""Testing Scala conversion of
        Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
        match l with
        |  nil => (x, nil)
        |  h::t => if x <=? h
                       then let ' pair j l2 := select x t in (j, h::l2)
                       else let ' pair j l2 := select h t in (j, x::l2)
        end.
       """) {
    CoqParser("""
        Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
        match l with
        |  nil => (x, nil)
        |  h::t => if x <=? h
                       then let ' pair j l2 := select x t in (j, h::l2)
                       else let ' pair j l2 := select h t in (j, x::l2)
        end.
      """) should generateScalaCode("""
      "def select(x: Nat, l: List[Nat]): (Nat, List[Nat]) =
      "  l match {
      "    case Nil => (x, Nil)
      "    case h :: t => if (x <= h) {
      "      val Tuple2(j, l2) = select(x, t)
      "      (j, h :: l2)
      "    }
      "    else {
      "      val Tuple2(j, l2) = select(h, t)
      "      (j, x :: l2)
      "    }
      "  }
      """)
  }

  test("""Testing Scala conversion of
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
      """) should generateScalaCode("""
        "sealed abstract class Tree
        "case object Leaf extends Tree
        "case class Node(l: Tree, r: Tree) extends Tree
        "def size(t: Tree): Nat =
        "  t match {
        "    case Leaf => 1
        "    case Node(l, r) => 1 + (size(l) + size(r))
        "  }
        """)
  }

  test("""Testing Scala conversion of
        Inductive Tree :=
          Leaf (value: nat) : Tree
        | Node(l r : Tree): Tree.

        Fixpoint addToLeaves (t: Tree) (n: nat) : Tree :=
        match t with
          | Leaf v => Leaf (v + n)
          | Node l r => Node (addToLeaves l n) (addToLeaves r n)
        end.
       """) {
    CoqParser("""
      Inductive Tree :=
        Leaf (value: nat) : Tree
      | Node(l r : Tree): Tree.

      Fixpoint addToLeaves (t: Tree) (n: nat) : Tree :=
      match t with
        | Leaf v => Leaf (v + n)
        | Node l r => Node (addToLeaves l n) (addToLeaves r n)
      end.
      """) should generateScalaCode("""
        "sealed abstract class Tree
        "case class Leaf(value: Nat) extends Tree
        "case class Node(l: Tree, r: Tree) extends Tree
        "def addToLeaves(t: Tree, n: Nat): Tree =
        "  t match {
        "    case Leaf(v) => Leaf(v + n)
        "    case Node(l, r) => Node(addToLeaves(l, n), addToLeaves(r, n))
        "  }
        """)
  }

  test("""Testing Scala conversion of "Fixpoint right {A : Type} (l r : A) := r." """) {
    CoqParser("Fixpoint right {A : Type} (l r : A) := r.") should
      generateScalaCode("def right[A](l: A, r: A) = r")
  }

  test("""Testing Scala conversion of
        Fixpoint elements_aux {V} (s: tree V) (base: list (nat * V)) : list (nat * V) :=
         match s with
         | E => base
         | T a k v b => elements_aux a ((k,v) :: elements_aux b base)
         end.
       """) {
    CoqParser("""
        Fixpoint elements_aux {V} (s: tree V) (base: list (nat * V)) : list (nat * V) :=
         match s with
         | E => base
         | T a k v b => elements_aux a ((k,v) :: elements_aux b base)
         end.
      """) should generateScalaCode("""
        "def elements_aux[V](s: tree[V], base: List[(Nat, V)]): List[(Nat, V)] =
        "  s match {
        "    case E => base
        "    case T(a, k, v, b) => elements_aux(a, (k, v) :: elements_aux(b, base))
        "  }
        """)
  }

  test("""Testing Scala conversion of
        Definition idTuple(tuple : nat * nat * bool) := tuple.
        Definition example := idTuple(1, 3, true).
       """) {
    CoqParser("""
        Definition idTuple(tuple : nat * nat * bool) := tuple.
        Definition example := idTuple(1, 3, true).
      """) should generateScalaCode("""
        "def idTuple(tuple: (Nat, Nat, Boolean)) = tuple
        "def example = idTuple((1, 3, true))
        """)
  }

  test("""Testing Scala conversion of
        Definition idTuple(tuple : nat * nat * bool * list nat) (dummyParam: nat) := tuple.
        Definition example := idTuple (1, 3, true, 3 :: nil) 7.
       """) {
    CoqParser("""
        Definition idTuple(tuple : nat * nat * bool * list nat) (dummyParam: nat) := tuple.
        Definition example := idTuple (1, 3, true, 3 :: nil) 7.
      """) should generateScalaCode("""
        "def idTuple(tuple: (Nat, Nat, Boolean, List[Nat]), dummyParam: Nat) = tuple
        "def example = idTuple((1, 3, true, 3 :: Nil), 7)
        """)
  }

  test("""Testing Scala conversion of
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
      """) should generateScalaCode("""
        "def matchOnTuple(tuple: (Nat, Nat)) =
        "  tuple match {
        "    case (Zero, Zero) => 5
        "    case (_, _)       => 7
        "  }
        """)
  }

  test("""Testing Scala conversion of
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
      """) should generateScalaCode("""
        "def matchOnTuple(x: Nat, y: Nat) =
        "  (x, y) match {
        "    case (Zero, Zero) => 5
        "    case (_, _)       => 7
        "  }
        """)
  }

  test("""Testing Scala conversion of
        Fixpoint sum (a b : nat) : nat :=
        match a with
          | 0 => b
          | S n => (sum n (S b))
        end.
       """) {
    CoqParser("""
        Fixpoint sum (a b : nat) : nat :=
        match a with
          | 0 => b
          | S n => (sum n (S b))
        end.
      """) should generateScalaCode("""
         "def sum(a: Nat, b: Nat): Nat =
         "  a match {
         "  case Zero => b
         "  case S(n) => sum(n, S(b))
         " }
        """)
  }

  /*
   *   TODO(Joseph Bakouny): Fix the empty case class issue:
   *   An empty case class is not generated with the correct parenthesis "()".
   *
   *   This is probably an issue with treehugger.scala.
   */
  ignore("""Testing Scala conversion of
          Inductive Tree {A : Type} :=
            Leaf
          | Node (info: A) (left: @Tree A) (right: @ Tree A).
       """) {
    CoqParser("""
          Inductive Tree {A : Type} :=
            Leaf
          | Node (info: A) (left: @Tree A) (right: @ Tree A).
      """) should generateScalaCode("""
        "sealed abstract class Tree[A]
        "case class Leaf[A]() extends Tree[A]
        "case class Node[A](info: A, l: Tree[A], r: Tree[A]) extends Tree[A]
        """)
  }

  test("""Testing Scala conversion of
      Inductive Tree :=
        Leaf (value: nat) : Tree
      | Node(l r : Tree): Tree.

      Fixpoint testFunction (t: Tree) : Tree :=
      match t with
        | Leaf (1 | 2 | 3) => Leaf 5
        | _ => Leaf 7
      end.
       """) {
    CoqParser("""
      Inductive Tree :=
        Leaf (value: nat) : Tree
      | Node(l r : Tree): Tree.

      Fixpoint testFunction (t: Tree) : Tree :=
      match t with
        | Leaf (1 | 2 | 3) => Leaf 5
        | _ => Leaf 7
      end.
      """) should generateScalaCode("""
        "sealed abstract class Tree
        "case class Leaf(value: Nat) extends Tree
        "case class Node(l: Tree, r: Tree) extends Tree
        "def testFunction(t: Tree): Tree =
        "  t match {
        "    case Leaf(S(Zero) | S(S(Zero)) | S(S(S(Zero)))) => Leaf(5)
        "    case _ => Leaf(7)
        "  }
        """)
  }

  test("""Testing Scala conversion of
      Inductive Tree :=
        Leaf (value: nat) : Tree
      | Node(l r : Tree): Tree.

      Fixpoint testFunction (t: Tree) : Tree :=
      match t with
        | Leaf 1 | Leaf 2 | Leaf 3 => Leaf 5
        | _ => Leaf 7
      end.
       """) {
    CoqParser("""
      Inductive Tree :=
        Leaf (value: nat) : Tree
      | Node(l r : Tree): Tree.

      Fixpoint testFunction (t: Tree) : Tree :=
      match t with
        | Leaf 1 | Leaf 2 | Leaf 3 => Leaf 5
        | _ => Leaf 7
      end.
      """) should generateScalaCode("""
        "sealed abstract class Tree
        "case class Leaf(value: Nat) extends Tree
        "case class Node(l: Tree, r: Tree) extends Tree
        "def testFunction(t: Tree): Tree =
        "  t match {
        "    case Leaf(S(Zero)) | Leaf(S(S(Zero))) | Leaf(S(S(S(Zero)))) => Leaf(5)
        "    case _ => Leaf(7)
        "  }
        """)
  }

  test("""Testing Scala conversion of
              Inductive Tree {A B : Type} : Type :=
              | Leaf (value: A) : Tree
              | Node (info: B) (left: @Tree A B) (right: @Tree A B) : Tree.
       """) {
    CoqParser("""
              Inductive Tree {A B : Type} : Type :=
              | Leaf (value: A) : Tree
              | Node (info: B) (left: @Tree A B) (right: @Tree A B) : Tree.
      """) should generateScalaCode("""
        "sealed abstract class Tree[A, B]
        "case class Leaf[A, B](value: A) extends Tree[A, B]
        "case class Node[A, B](info: B, left: Tree[A, B], right: Tree[A, B]) extends Tree[A, B]
        """)
  }

  test("""Testing Scala conversion of
          Inductive Tree {A B : Type} : Type :=
          | Leaf {C : Type} (firstValue: A) (secondValue: C)
          | Node {D} (firstValue: B) (secondValue: D) (left: @Tree A B) (right: @Tree A B) : Tree.
       """) {
    CoqParser("""
          Inductive Tree {A B : Type} : Type :=
          | Leaf {C : Type} (firstValue: A) (secondValue: C)
          | Node {D} (firstValue: B) (secondValue: D) (left: @Tree A B) (right: @Tree A B) : Tree.
      """) should generateScalaCode("""
        "sealed abstract class Tree[A, B]
        "case class Leaf[A, B, C](firstValue: A, secondValue: C) extends Tree[A, B]
        "case class Node[A, B, D](firstValue: B, secondValue: D, left: Tree[A, B], right: Tree[A, B]) extends Tree[A, B]
        """)
  }

  test("""Testing Scala conversion of
        Definition f (a: nat) := a + 1.

        Definition g : nat -> nat := f.
       """) {
    CoqParser("""
        Definition f (a: nat) := a + 1.

        Definition g : nat -> nat := f.
      """) should generateScalaCode("""
        "def f(a: Nat) = a + 1
        "def g: Nat => Nat = f
        """)
  }

  test("""Testing Scala conversion of
      Lemma size_left (l r : Tree): size (Node l r) > (size l).
      Proof.
        intros.
        induction l.
        - simpl; omega.
        - simpl; omega.
      Qed.
       """) {
    CoqParser("""
      Lemma size_left (l r : Tree): (size (Node l r)) > (size l).
      Proof.
        intros.
        induction l.
        - simpl; omega.
        - simpl; omega.
      Qed.
      """) should generateScalaCode("")
  }

  test("""Testing Scala conversion of
      Inductive Tree : Type :=
        Leaf : Tree
      | Node(l r : Tree): Tree.

      Fixpoint size (t: Tree) : nat :=
      match t with
        Leaf => 1
      | Node l r => 1 + (size l) + (size r)
      end.

      Lemma size_left (l r : Tree): size (Node l r) > (size l).
      Proof.
        intros.
        induction l.
        - simpl; omega.
        - simpl; omega.
      Qed.
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

      Lemma size_left (l r : Tree): (size (Node l r)) > (size l).
      Proof.
        intros.
        induction l.
        - simpl; omega.
        - simpl; omega.
      Qed.
      """) should generateScalaCode("""
        "sealed abstract class Tree
        "case object Leaf extends Tree
        "case class Node(l: Tree, r: Tree) extends Tree
        "def size(t: Tree): Nat =
        "  t match {
        "    case Leaf => 1
        "    case Node(l, r) => 1 + (size(l) + size(r))
        "  }
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
        "def size[A](t: Tree[A]): Nat =
        "  t match {
        "   case Leaf(_) => 1
        "   case Node(l, r) => 1 + (size(l) + size(r))
        "  }
        "def map[A, B](t: Tree[A], f: A => B): Tree[B] =
        "  t match {
        "    case Leaf(a) => Leaf(f(a))
        "    case Node(l, r) => Node(map(l, f), map(r, f))
        "  }
        """)
  }
}
