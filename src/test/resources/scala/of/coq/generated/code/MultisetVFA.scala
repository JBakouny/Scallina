import scala.of.coq.lang._
import Nat._
import Pairs._
import MoreLists._
object MultisetVFA {
  type value = Nat
  type multiset = value => Nat
  def empty: multiset =
    x => 0
  def union(a: multiset)(b: multiset): multiset =
    x => a(x) + b(x)
  def singleton(v: value): multiset =
    x => if (x == v) 1
    else 0
  def contents(al: List[value]): multiset =
    al match {
      case a :: bl => union(singleton(a))(contents(bl))
      case Nil => empty
    }
}

