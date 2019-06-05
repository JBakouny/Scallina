import scala.of.coq.lang._
import Nat._
import Pairs._
import Bools._
import MoreLists._
import scala.concurrent.Future
import MoreFutures._
object RandomAccessList {
  sealed abstract class Tree[+T]
  case class Leaf[T](v: T) extends Tree[T]
  case class Node[T](v: T, l: Tree[T], r: Tree[T]) extends Tree[T]
  object Node {
    def apply[T] =
      (v: T) => (l: Tree[T]) => (r: Tree[T]) => new Node(v, l, r)
  }
  sealed abstract class RAList[+T]
  case object RaNil extends RAList[Nothing]
  case class RaCons[T](t: Tree[T], e: Nat, l: RAList[T]) extends RAList[T]
  object RaCons {
    def apply[T] =
      (t: Tree[T]) => (e: Nat) => (l: RAList[T]) => new RaCons(t, e, l)
  }
  def head[T](l: RAList[T]): Option[T] =
    l match {
      case RaNil => None
      case RaCons(t, _, _) => t match {
        case Leaf(x) => Some(x)
        case Node(x, _, _) => Some(x)
      }
    }
  def cons[T](x: T)(l: RAList[T]): RAList[T] =
    l match {
      case RaNil => RaCons(Leaf(x))(0)(l)
      case RaCons(t, s, RaNil) => RaCons(Leaf(x))(0)(l)
      case RaCons(t1, h1, RaCons(t2, h2, q)) => if (h1 == h2) RaCons(Node(x)(t1)(t2))(1 + h1)(q)
      else RaCons(Leaf(x))(0)(l)
    }
  def tail[T](l: RAList[T]): RAList[T] =
    l match {
      case RaNil => RaNil
      case RaCons(t, h, q) => t match {
        case Leaf(_) => q
        case Node(_, t1, t2) => RaCons(t1)(h - 1)(RaCons(t2)(h - 1)(q))
      }
    }
}

