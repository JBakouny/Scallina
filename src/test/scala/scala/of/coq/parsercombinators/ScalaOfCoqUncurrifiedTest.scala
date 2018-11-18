package scala.of.coq.parsercombinators

import org.scalatest.FunSuite
import org.scalatest.Matchers.convertToAnyShouldWrapper

import scala.of.coq.parsercombinators.CustomMatchers.generateScalaCode
import scala.of.coq.parsercombinators.TestUtils.coqParserShouldFailToGenerateScalaCodeFor
import scala.of.coq.parsercombinators.compiler.NoCurrying
import scala.of.coq.parsercombinators.parser.CoqParser

class ScalaOfCoqUncurrifiedTest extends FunSuite {

  implicit val curryingStrategy: NoCurrying.type = NoCurrying

  /*
   * TODO(Joseph Bakouny) - Error handling:
   * Consider implementing a typechecker for the subset of Gallina that
   * we support in order to make sure that all Gallina constructions that do not conform to this subset
   * are explicitly rejected by Scallina's front end.
   *
   * Currently, a significant verification is made by Scallina's back-end which throws exceptions when
   * it encounters Gallina constructions that cannot be translated to Scala.
   */
  test(
    """Testing that explicit Type parameters are not supported if the return type is not Type
      Definition illegalFunction (x: Type) := x -> x.
       """) {
    coqParserShouldFailToGenerateScalaCodeFor(
      """
        Definition illegalFunction (x: Type) := x -> x.
        """)
  }

  test(
    """Testing Scala conversion of "Definition legalFunction (x: Type) : Type := x -> x." """) {
    CoqParser("Definition legalFunction (x: Type) : Type := x -> x.") should
      generateScalaCode("type legalFunction[x] = x => x")
  }

  test(
    """Testing Scala conversion of "Definition newTypeAlias : Type := nat -> nat." """) {
    CoqParser("Definition newTypeAlias : Type := nat -> nat.") should
      generateScalaCode("type newTypeAlias = Nat => Nat")
  }

  test("""Testing that explicit Prop parameters are not supported
      Definition illegalFunction (x: Prop) := 3.
       """) {
    coqParserShouldFailToGenerateScalaCodeFor(
      """
        Definition illegalFunction (x: Prop) := 3.
        """)
  }

  test("""Testing that explicit Set parameters are not supported
      Definition illegalFunction (x: Set) := 3.
       """) {
    coqParserShouldFailToGenerateScalaCodeFor(
      """
        Definition illegalFunction (x: Set) := 3.
        """)
  }

  test("""Testing that implicit value binders are not supported
      Definition illegalFunction {x: nat} (y : nat) := x + y.
       """) {
    coqParserShouldFailToGenerateScalaCodeFor(
      """
        Definition illegalFunction {x: nat} (y : nat) := x + y.
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

  test("""Testing Scala conversion of "Require Export Coq.Arith.PeanoNat." """) {
    CoqParser("Require Export Coq.Arith.PeanoNat.") should
      generateScalaCode("")
  }

  test("""Testing Scala conversion of "Load MyCoqProgram." """) {
    CoqParser("Load MyCoqProgram.") should
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

  test(
    """Testing Scala conversion of "Definition right {A : Type} (l r : A) := r." """) {
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

  test("""Testing Scala conversion of
        Definition add : Z -> Z -> Z :=
          fun (x : Z) => fun (y : Z) => x + y.
    """) {
    CoqParser("""
        Definition add : Z -> Z -> Z :=
          fun (x : Z) => fun (y : Z) => x + y.
      """) should generateScalaCode("""
      "def add: BigInt => BigInt => BigInt =
      "  (x: BigInt) => (y: BigInt) => x + y
      """)
  }

  test(
    """Testing Scala conversion of "Definition add(x y : nat) : nat := x + y." """) {
    CoqParser("""
          Definition add(x y : nat) : nat := x + y.
      """) should generateScalaCode("def add(x: Nat, y: Nat): Nat = x + y")
  }

  test(
    """Testing Scala conversion of "Definition add(x y z : nat) : nat := x + y." """) {
    CoqParser("""
          Definition add(x y z : nat) : nat := x + y + z.
      """) should generateScalaCode(
      "def add(x: Nat, y: Nat, z: Nat): Nat = x + (y + z)")
  }

  test(
    """Testing Scala conversion of "Definition addTen(n : nat) : nat := add n 10." """) {
    CoqParser("Definition addTen(n : nat) : nat := add n 10.") should
      generateScalaCode("def addTen(n: Nat): Nat = add(n, 10)")
  }

  test(
    """Testing Scala conversion of "Definition addTen(n : nat) : nat := (add n 10)." """) {
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
      """) should generateScalaCode(
      """
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
      """) should generateScalaCode(
      """
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
      """) should generateScalaCode(
      """
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
      """) should generateScalaCode(
      """
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
      """) should generateScalaCode(
      """
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
      """) should generateScalaCode(
      """
      "def testSimpleLetWithBinders(x: Nat): Nat = {
      " val f = (a: Nat) => 3 * a
      " 7 * f(x)
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
      """) should generateScalaCode(
      """
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
      """) should generateScalaCode(
      """
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
      Inductive Nat : Set :=
      | Zero
      | S (n: Nat).

      Definition pred (n : Nat) : Nat :=
        match n with
          | Zero => n
          | S u => u
        end.

      Fixpoint add (n m : Nat) : Nat :=
        match n with
        | Zero => m
        | S p => S (add p m)
        end.

      Fixpoint mul (n m : Nat) : Nat :=
        match n with
        | Zero => Zero
        | S p => add m (mul p m)
        end.

      Fixpoint sub (n m : Nat) : Nat :=
        match n, m with
        | S k, S l => sub k l
        | _, _ => n
        end.
       """) {
    CoqParser("""
      Inductive Nat : Set :=
      | Zero
      | S (n: Nat).

      Definition pred (n : Nat) : Nat :=
        match n with
          | Zero => n
          | S u => u
        end.

      Fixpoint add (n m : Nat) : Nat :=
        match n with
        | Zero => m
        | S p => S (add p m)
        end.

      Fixpoint mul (n m : Nat) : Nat :=
        match n with
        | Zero => Zero
        | S p => add m (mul p m)
        end.

      Fixpoint sub (n m : Nat) : Nat :=
        match n, m with
        | S k, S l => sub k l
        | _, _ => n
        end.
      """) should generateScalaCode("""
        "sealed abstract class Nat
        "case object Zero extends Nat
        "case class S(n: Nat) extends Nat
        "def pred(n: Nat): Nat =
        "  n match {
        "    case Zero => n
        "    case S(u) => u
        "  }
        "def add(n: Nat, m: Nat): Nat =
        "  n match {
        "    case Zero => m
        "    case S(p) => S(add(p, m))
        "  }
        "def mul(n: Nat, m: Nat): Nat =
        "  n match {
        "    case Zero => Zero
        "    case S(p) => add(m, mul(p, m))
        "  }
        "def sub(n: Nat, m: Nat): Nat =
        "  (n, m) match {
        "    case (S(k), S(l)) => sub(k, l)
        "    case (_, _)       => n
        "  }
        """)
  }

  test("""Testing Scala conversion of
        Inductive Tree : Type :=
          Leaf
        | Node(l r : Tree).

        Fixpoint size (t: Tree) : nat :=
        match t with
          Leaf => 1
        | Node l r => 1 + (size l) + (size r)
        end.
       """) {
    CoqParser("""
        Inductive Tree : Type :=
          Leaf
        | Node(l r : Tree).

        Fixpoint size (t: Tree) : nat :=
        match t with
          Leaf => 1
        | Node l r => 1 + (size l) + (size r)
        end.
      """) should generateScalaCode(
      """
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
          Leaf (value: nat)
        | Node(l r : Tree).

        Fixpoint addToLeaves (t: Tree) (n: nat) : Tree :=
        match t with
          | Leaf v => Leaf (v + n)
          | Node l r => Node (addToLeaves l n) (addToLeaves r n)
        end.
       """) {
    CoqParser("""
      Inductive Tree :=
        Leaf (value: nat)
      | Node(l r : Tree).

      Fixpoint addToLeaves (t: Tree) (n: nat) : Tree :=
      match t with
        | Leaf v => Leaf (v + n)
        | Node l r => Node (addToLeaves l n) (addToLeaves r n)
      end.
      """) should generateScalaCode(
      """
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

  test(
    """Testing Scala conversion of "Fixpoint right {A : Type} (l r : A) := r." """) {
    CoqParser("Fixpoint right {A : Type} (l r : A) := r.") should
      generateScalaCode("def right[A](l: A, r: A) = r")
  }

  test(
    """Testing Scala conversion of
        Fixpoint elements_aux {V} (s: tree V) (base: list (nat * V)) : list (nat * V) :=
         match s with
         | E => base
         | T a k v b => elements_aux a ((k,v) :: elements_aux b base)
         end.
       """) {
    CoqParser(
      """
        Fixpoint elements_aux {V} (s: tree V) (base: list (nat * V)) : list (nat * V) :=
         match s with
         | E => base
         | T a k v b => elements_aux a ((k,v) :: elements_aux b base)
         end.
      """) should generateScalaCode(
      """
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
      """) should generateScalaCode(
      """
        "def idTuple(tuple: (Nat, Nat, Boolean)) = tuple
        "def example = idTuple((1, 3, true))
        """)
  }

  test(
    """Testing Scala conversion of
        Definition idTuple(tuple : nat * nat * bool * list nat) (dummyParam: nat) := tuple.
        Definition example := idTuple (1, 3, true, 3 :: nil) 7.
       """) {
    CoqParser(
      """
        Definition idTuple(tuple : nat * nat * bool * list nat) (dummyParam: nat) := tuple.
        Definition example := idTuple (1, 3, true, 3 :: nil) 7.
      """) should generateScalaCode(
      """
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

  test("""Testing Scala conversion of
          Inductive Tree {A : Type} :=
            Leaf
          | Node (info: A) (left: @Tree A) (right: @ Tree A).
       """) {
    CoqParser("""
          Inductive Tree {A : Type} :=
            Leaf
          | Node (info: A) (left: @Tree A) (right: @ Tree A).
      """) should generateScalaCode(
      """
        "sealed abstract class Tree[+A]
        "case object Leaf extends Tree[Nothing]
        "case class Node[A](info: A, left: Tree[A], right: Tree[A]) extends Tree[A]
        """)
  }

  test("""Testing Scala conversion of
      Inductive Tree :=
        Leaf (value: nat)
      | Node(l r : Tree).

      Fixpoint testFunction (t: Tree) : Tree :=
      match t with
        | Leaf (1 | 2 | 3) => Leaf 5
        | _ => Leaf 7
      end.
       """) {
    CoqParser("""
      Inductive Tree :=
        Leaf (value: nat)
      | Node(l r : Tree).

      Fixpoint testFunction (t: Tree) : Tree :=
      match t with
        | Leaf (1 | 2 | 3) => Leaf 5
        | _ => Leaf 7
      end.
      """) should generateScalaCode(
      """
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
        Leaf (value: nat)
      | Node(l r : Tree)

      Fixpoint testFunction (t: Tree) : Tree :=
      match t with
        | Leaf 1 | Leaf 2 | Leaf 3 => Leaf 5
        | _ => Leaf 7
      end.
       """) {
    CoqParser("""
      Inductive Tree :=
        Leaf (value: nat)
      | Node(l r : Tree).

      Fixpoint testFunction (t: Tree) : Tree :=
      match t with
        | Leaf 1 | Leaf 2 | Leaf 3 => Leaf 5
        | _ => Leaf 7
      end.
      """) should generateScalaCode(
      """
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
              | Leaf (value: A)
              | Node (info: B) (left: @Tree A B) (right: @Tree A B).
       """) {
    CoqParser("""
              Inductive Tree {A B : Type} : Type :=
              | Leaf (value: A)
              | Node (info: B) (left: @Tree A B) (right: @Tree A B).
      """) should generateScalaCode(
      """
        "sealed abstract class Tree[+A, +B]
        "case class Leaf[A, B](value: A) extends Tree[A, B]
        "case class Node[A, B](info: B, left: Tree[A, B], right: Tree[A, B]) extends Tree[A, B]
        """)
  }

  test(
    """Testing Scala conversion of
          Inductive Tree {A B : Type} : Type :=
          | Leaf {C : Type} (firstValue: A) (secondValue: C)
          | Node {D} (firstValue: B) (secondValue: D) (left: @Tree A B) (right: @Tree A B).
       """) {
    CoqParser("""
          Inductive Tree {A B : Type} : Type :=
          | Leaf {C : Type} (v1: A) (v2: C)
          | Node {D} (v1: B) (v2: D) (l: @Tree A B) (r: @Tree A B).
      """) should generateScalaCode(
      """
        "sealed abstract class Tree[+A, +B]
        "case class Leaf[A, B, C](v1: A, v2: C) extends Tree[A, B]
        "case class Node[A, B, D](v1: B, v2: D, l: Tree[A, B], r: Tree[A, B]) extends Tree[A, B]
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
        Leaf
      | Node(l r : Tree).

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
        Leaf
      | Node(l r : Tree).

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
      """) should generateScalaCode(
      """
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
      """) should generateScalaCode(
      """
        "sealed abstract class Tree[+A]
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

  test(
    """Testing Scala conversion of
        (*
        Inspired from:
        https://www.cs.princeton.edu/~appel/vfa/Redblack.html
        *)

        Require Import Coq.ZArith.ZArith.

        Local Open Scope Z_scope.

        Inductive color := Red | Black.

        Inductive tree V : Type :=
        | E
        | T(c: color) (l: tree V) (key: Z) (value: V) (r: tree V).

        Arguments E {V}.
        Arguments T {V} _ _ _ _ _.

        Fixpoint lookup {V} (default: V) (x: Z) (t : tree V) : V :=
          match t with
          | E => default
          | T _ tl k v tr => if (x <? k) then lookup default x tl
                                 else if (k <? x) then lookup default x tr
                                 else v
          end.

        Definition balance {V} (rb : color) (t1: tree V) (k : Z) (vk: V) (t2: tree V) : tree V:=
         match rb with Red => T Red t1 k vk t2
         | _ =>
         match t1 with
         | T Red (T Red a x vx b) y vy c =>
              T Red (T Black a x vx b) y vy (T Black c k vk t2)
         | T Red a x vx (T Red b y vy c) =>
              T Red (T Black a x vx b) y vy (T Black c k vk t2)
         | a => match t2 with
                    | T Red (T Red b y vy c) z vz d =>
                  T Red (T Black t1 k vk b) y vy (T Black c z vz d)
                    | T Red b y vy (T Red c z vz d)  =>
                  T Red (T Black t1 k vk b) y vy (T Black c z vz d)
                    | _ => T Black t1 k vk t2
                    end
          end
         end.

        Definition makeBlack {V} (t : tree V) : tree V :=
          match t with
          | E => E
          | T _ a x vx b => T Black a x vx b
          end.

        Fixpoint ins {V} (x : Z) (vx: V) (s: tree V) : tree V :=
         match s with
         | E => T Red E x vx E
         | T c a y vy b => if (x <? y) then balance c (ins x vx a) y vy b
                                else if (y <? x) then balance c a y vy (ins x vx b)
                                else T c a x vx b
         end.

        Definition insert {V} (x : Z) (vx : V) (s : tree V) : tree V := makeBlack (ins x vx s).

       """) {
    CoqParser(
      """
        (*
        Inspired from:
        https://www.cs.princeton.edu/~appel/vfa/Redblack.html
        *)

        Require Import Coq.ZArith.ZArith.

        Local Open Scope Z_scope.

        Inductive color := Red | Black.

        Inductive tree V : Type :=
        | E
        | T(c: color) (l: tree V) (key: Z) (value: V) (r: tree V).

        Arguments E {V}.
        Arguments T {V} _ _ _ _ _.

        Fixpoint lookup {V} (default: V) (x: Z) (t : tree V) : V :=
          match t with
          | E => default
          | T _ tl k v tr => if (x <? k) then lookup default x tl
                                 else if (k <? x) then lookup default x tr
                                 else v
          end.

        Definition balance {V} (rb : color) (t1: tree V) (k : Z) (vk: V) (t2: tree V) : tree V:=
         match rb with Red => T Red t1 k vk t2
         | _ =>
         match t1 with
         | T Red (T Red a x vx b) y vy c =>
              T Red (T Black a x vx b) y vy (T Black c k vk t2)
         | T Red a x vx (T Red b y vy c) =>
              T Red (T Black a x vx b) y vy (T Black c k vk t2)
         | a => match t2 with
                    | T Red (T Red b y vy c) z vz d =>
                  T Red (T Black t1 k vk b) y vy (T Black c z vz d)
                    | T Red b y vy (T Red c z vz d)  =>
                  T Red (T Black t1 k vk b) y vy (T Black c z vz d)
                    | _ => T Black t1 k vk t2
                    end
          end
         end.

        Definition makeBlack {V} (t : tree V) : tree V :=
          match t with
          | E => E
          | T _ a x vx b => T Black a x vx b
          end.

        Fixpoint ins {V} (x : Z) (vx: V) (s: tree V) : tree V :=
         match s with
         | E => T Red E x vx E
         | T c a y vy b => if (x <? y) then balance c (ins x vx a) y vy b
                                else if (y <? x) then balance c a y vy (ins x vx b)
                                else T c a x vx b
         end.

        Definition insert {V} (x : Z) (vx : V) (s : tree V) : tree V := makeBlack (ins x vx s).

      """) should generateScalaCode(
      """
        "sealed abstract class color
        "case object Red extends color
        "case object Black extends color
        "sealed abstract class tree[+V]
        "case object E extends tree[Nothing]
        "case class T[V](c: color, l: tree[V], key: BigInt, value: V, r: tree[V]) extends tree[V]
        "def lookup[V](default: V, x: BigInt, t: tree[V]): V =
        "  t match {
        "    case E => default
        "    case T(_, tl, k, v, tr) => if ((x < k)) lookup(default, x, tl)
        "    else if ((k < x)) lookup(default, x, tr)
        "    else v
        "  }
        "def balance[V](rb: color, t1: tree[V], k: BigInt, vk: V, t2: tree[V]): tree[V] =
        "  rb match {
        "    case Red => T(Red, t1, k, vk, t2)
        "    case _ => t1 match {
        "      case T(Red, T(Red, a, x, vx, b), y, vy, c) => T(Red, T(Black, a, x, vx, b), y, vy, T(Black, c, k, vk, t2))
        "      case T(Red, a, x, vx, T(Red, b, y, vy, c)) => T(Red, T(Black, a, x, vx, b), y, vy, T(Black, c, k, vk, t2))
        "      case a => t2 match {
        "        case T(Red, T(Red, b, y, vy, c), z, vz, d) => T(Red, T(Black, t1, k, vk, b), y, vy, T(Black, c, z, vz, d))
        "        case T(Red, b, y, vy, T(Red, c, z, vz, d)) => T(Red, T(Black, t1, k, vk, b), y, vy, T(Black, c, z, vz, d))
        "        case _                                     => T(Black, t1, k, vk, t2)
        "      }
        "    }
        "  }
        "def makeBlack[V](t: tree[V]): tree[V] =
        "  t match {
        "    case E                 => E
        "    case T(_, a, x, vx, b) => T(Black, a, x, vx, b)
        "  }
        "def ins[V](x: BigInt, vx: V, s: tree[V]): tree[V] =
        "  s match {
        "    case E => T(Red, E, x, vx, E)
        "    case T(c, a, y, vy, b) => if ((x < y)) balance(c, ins(x, vx, a), y, vy, b)
        "    else if ((y < x)) balance(c, a, y, vy, ins(x, vx, b))
        "    else T(c, a, x, vx, b)
        "  }
        "def insert[V](x: BigInt, vx: V, s: tree[V]): tree[V] = makeBlack(ins(x, vx, s))
        """)
  }
}
