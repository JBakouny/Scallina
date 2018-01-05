import scala.of.coq.lang._
import Nat._
import Pairs._
import MoreLists._
import scala.concurrent.Future
import MoreFutures._
object MergeWithFunction {
  def merge[A](less: A => A => Boolean)(z: (List[A], List[A])): List[A] = {
    val (l1, l2) = z
    l1 match {
      case Nil => l2
      case x1 :: l1_ => l2 match {
        case Nil => l1
        case x2 :: l2_ => if (less(x1)(x2)) x1 :: merge(less)((l1_, l2))
        else x2 :: merge(less)((l1, l2_))
      }
    }
  }
}

