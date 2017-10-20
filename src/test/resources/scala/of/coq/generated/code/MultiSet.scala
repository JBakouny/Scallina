import scala.of.coq.lang._
import Nat._
import Pairs._
import MoreLists._
object MultiSet {
  def empty: Nat => Nat =
    x => 0
  def union(a: Nat => Nat)(b: Nat => Nat): Nat => Nat =
    x => a(x) + b(x)
  def singleton(v: Nat): Nat => Nat =
    x => if (x == v) 1
    else 0
  def contents(al: List[Nat]): Nat => Nat =
    al match {
      case a :: bl => union(singleton(a))(contents(bl))
      case Nil => empty
    }
  def list_delete(al: List[Nat])(v: Nat): List[Nat] =
    al match {
      case x :: bl => if (x == v) bl
      else x :: list_delete(bl)(v)
      case Nil => Nil
    }
  def multiset_delete(m: Nat => Nat)(v: Nat) =
    (x: Nat) => if (x == v) pred(m(x))
    else m(x)
}

