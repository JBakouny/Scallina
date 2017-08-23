import scala.of.coq.lang._
import Nat._
import MoreLists._
object SimpleMapImplementation {
  def map[A, B](l: List[A])(f: A => B): List[B] =
    l match {
      case Nil => Nil
      case x :: xs => f(x) :: map(xs)(f)
    }
}

