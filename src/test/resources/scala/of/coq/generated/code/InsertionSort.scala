import scala.of.coq.lang._
import Nat._
import MoreLists._
object InsertionSort {
  def insert(i: Nat, l: List[Nat]): List[Nat] =
    l match {
      case Nil => i :: Nil
      case h :: t => if (i <= h) i :: (h :: t)
      else h :: insert(i, t)
    }
  def sort(l: List[Nat]): List[Nat] =
    l match {
      case Nil => Nil
      case h :: t => insert(h, sort(t))
    }
}

