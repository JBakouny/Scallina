import scala.of.coq.lang._
import Nat._
import MoreLists._
object InductiveDefinitionWithZ {
  sealed abstract class Tree[A]
  case class Leaf[A](value: A) extends Tree[A]
  case class Node[A](l: Tree[A], r: Tree[A]) extends Tree[A]
  object Node {
    def apply[A] =
      (l: Tree[A]) => (r: Tree[A]) => new Node(l, r)
  }
  def size[A](t: Tree[A]): BigInt =
    t match {
      case Leaf(_) => 1
      case Node(l, r) => 1 + (size(l) + size(r))
    }
}

