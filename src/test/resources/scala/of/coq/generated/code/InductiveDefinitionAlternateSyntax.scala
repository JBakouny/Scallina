import scala.of.coq.lang._
import Nat._
import Pairs._
import MoreLists._
object InductiveDefinitionAlternateSyntax {
  sealed abstract class Tree[A]
  case class Leaf[A](value: A) extends Tree[A]
  case class Node[A](l: Tree[A], r: Tree[A]) extends Tree[A]
  object Node {
    def apply[A] =
      (l: Tree[A]) => (r: Tree[A]) => new Node(l, r)
  }
  def size[A](t: Tree[A]): Nat =
    t match {
      case Leaf(_) => 1
      case Node(l, r) => 1 + (size(l) + size(r))
    }
  def map[A, B](t: Tree[A])(f: A => B): Tree[B] =
    t match {
      case Leaf(a) => Leaf(f(a))
      case Node(l, r) => Node(map(l)(f))(map(r)(f))
    }
}

