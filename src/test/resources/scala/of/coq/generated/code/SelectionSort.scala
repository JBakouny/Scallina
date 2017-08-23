import scala.of.coq.lang._
import Nat._
import MoreLists._
object SelectionSort {
  def select(x: Nat)(l: List[Nat]): (Nat, List[Nat]) =
    l match {
      case Nil => (x, Nil)
      case h :: t => if (x <= h) {
        val (j, l2) = select(x)(t)
        (j, h :: l2)
      }
      else {
        val (j, l2) = select(h)(t)
        (j, x :: l2)
      }
    }
  def selsort(l: List[Nat])(n: Nat): List[Nat] =
    (l, n) match {
      case (x :: r, S(n2)) => {
        val (y, r2) = select(x)(r)
        y :: selsort(r2)(n2)
      }
      case (Nil, _) => Nil
      case (_ :: _, Zero) => Nil
    }
  def selection_sort(l: List[Nat]) = selsort(l)(length(l))
}

