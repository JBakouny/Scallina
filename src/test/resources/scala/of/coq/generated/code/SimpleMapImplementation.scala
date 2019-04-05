import scala.of.coq.lang._
import Nat._
import Pairs._
import Bools._
import MoreLists._
import scala.concurrent.Future
import MoreFutures._
object SimpleMapImplementation {
  def map[A, B](l: List[A])(f: A => B): List[B] =
    l match {
      case Nil => Nil
      case x :: xs => f(x) :: map(xs)(f)
    }
}

