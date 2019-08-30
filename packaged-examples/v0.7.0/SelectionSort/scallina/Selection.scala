import scala.of.coq.lang._
import Nat._
import Pairs._
import Bools._
import MoreLists._
import scala.concurrent.Future
import MoreFutures._
object Selection {
  def select(x: Nat)(l: List[Nat]): (Nat, List[Nat]) =
    l match {
      case Nil => (x, Nil)
      case h :: t => if (x <= h) {
        val (j, l1) = select(x)(t)
        (j, h :: l1)
      }
      else {
        val (j, l1) = select(h)(t)
        (j, x :: l1)
      }
    }
  def selsort(l: List[Nat])(n: Nat): List[Nat] =
    (l, n) match {
      case (x :: r, S(n1)) => {
        val (y, r1) = select(x)(r)
        y :: selsort(r1)(n1)
      }
      case (Nil, _) => Nil
      case (_ :: _, Zero) => Nil
    }
  def selection_sort(l: List[Nat]): List[Nat] = selsort(l)(length(l))
}

