import scala.of.coq.lang._
import Nat._
import Pairs._
import Bools._
import MoreLists._
import scala.concurrent.Future
import MoreFutures._
object RandomAccessList {
  sealed abstract class RandomAccessList[+E]
  case object Empty extends RandomAccessList[Nothing]
  case class Cons[E](one: Boolean, e: E, s: RandomAccessList[(E, E)]) extends RandomAccessList[E]
  object Cons {
    def apply[E] =
      (one: Boolean) => (e: E) => (s: RandomAccessList[(E, E)]) => new Cons(one, e, s)
  }
  def length[E](l: RandomAccessList[E]): Nat =
    l match {
      case Empty => 0
      case Cons(one, e, s) => 2 * (length(s) + (if (one) 1
      else 0))
    }
  def get[E](i: Nat)(l: RandomAccessList[E]): Option[E] =
    l match {
      case Empty => None
      case Cons(one, e, s) => if ((one)) if (eqb(i)(0)) Some(e)
      else get(div(i - 1)(2))(s) match {
        case None => None
        case Some((x1, x2)) => Some(if (eqb(modulo(i)(2))(1)) x1
        else x2)
      }
      else get(div(i)(2))(s) match {
        case None => None
        case Some((x1, x2)) => Some(if (eqb(modulo(i)(2))(0)) x1
        else x2)
      }
    }
  def add[E](x: E)(l: RandomAccessList[E]): RandomAccessList[E] =
    l match {
      case Empty => Cons(true)(x)(Empty)
      case Cons(one, e, s) => if (one) Cons(false)(x)(add((x, e))(s))
      else Cons(true)(x)(s)
    }
}

