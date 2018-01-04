import scala.of.coq.lang._
import Nat._
import Pairs._
import MoreLists._
import scala.concurrent.Future
import MoreFutures._
object FutureMergeSort {
  def split[A](l: List[A]): (List[A], List[A]) =
    l match {
      case Nil => (Nil, Nil)
      case x :: Nil => (x :: Nil, Nil)
      case x :: y :: xs => {
        val (l1, l2) = split(xs)
        (x :: l1, y :: l2)
      }
    }
  def merge(z: (List[Nat], List[Nat])): List[Nat] = {
    val (l1, l2) = z
    l1 match {
      case Nil => l2
      case x1 :: l1_ => l2 match {
        case Nil => l1
        case x2 :: l2_ => if (x1 <= x2) x1 :: merge((l1_, l2))
        else x2 :: merge((l1, l2_))
      }
    }
  }
  def msort(l: List[Nat])(n: Nat): Future[List[Nat]] =
    (l, n) match {
      case (Nil, _) => future(Nil)
      case (x :: Nil, _) => future(x :: Nil)
      case (x :: y :: _, S(n1)) => {
        val (l1, l2) = split(l)
        fut_flat_map((r1: List[Nat]) => fut_map((r2: List[Nat]) => merge((r1, r2)))(msort(l2)(n1)))(msort(l1)(n1))
      }
      case (_ :: _ :: _, Zero) => future(Nil)
    }
  def mergeSort(l: List[Nat]): Future[List[Nat]] = msort(l)(length(l))
}

