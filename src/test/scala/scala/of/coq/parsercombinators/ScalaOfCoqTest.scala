package scala.of.coq.parsercombinators

import scala.of.coq.parsercombinators.compiler.ScalaOfCoq
import scala.of.coq.parsercombinators.parser.CoqParser

import org.scalatest.Finders
import org.scalatest.FunSuite
import org.scalatest.Matchers.convertToAnyShouldWrapper

import CustomMatchers.generateScalaCode

class ScalaOfCoqTest extends FunSuite {

  def coqParserShouldFailToGenerateScalaCodeFor(coqCode: String) {
    val parseResult = CoqParser(coqCode)
    assertThrows[IllegalStateException] {
      parseResult.map(ScalaOfCoq.toScalaCode(_))
    }
  }

  test("""Testing that explicit Type parameters are not supported
      Definition illegalFunction (x: Type) := 3.
       """) {
    coqParserShouldFailToGenerateScalaCodeFor("""
        Definition illegalFunction (x: Type) := 3.
        """)
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

  test("""Testing Scala conversion of "Require Import Coq.Arith.PeanoNat." """) {
    CoqParser("Require Import Coq.Arith.PeanoNat.") should
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

  /*
   * TODO (Joseph Bakouny): Handle Nats in pattern position correctly
   * Nat wrapper should be implemented
   * type Nat = BigInt + negative number check + overflow control
   * Our implementation should extend trait Numeric or Integral (+ faire la meme chose pour les listes)
   * Voir ce qu'on a fait avec Isabelle Code Generation pour les nats
   * Voir ce qu'on a fait avec Leon pour les listes (pourquoi pas les listes de Scala, est-ce que c'est pour les generiques?)
   */
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
   *   TODO(Joseph Bakouny): Fix an issue where an empty case class with generic type params is not generated
   *     with the correct parenthesis "()".
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
        "case class Node[A](l: Tree[A], r: Tree[A]) extends Tree[A]
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
        " t match {
        " case Leaf(S(S(S(Zero))) | S(S(Zero)) | S(Zero)) => Leaf(5)
        " case _ => Leaf(7)
        " }
        """)
  }

  // TODO (Joseph Bakouny): Handle several multPatterns in an equation
  ignore("""Testing Scala conversion of
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
        "    case Leaf(3) | Leaf(2) | Leaf(1) => Leaf(5)
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
}
