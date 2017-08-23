import scala.of.coq.lang._
import Nat._
import MoreLists._
object AmortizedQueue {
  sealed abstract class List
  case class Cons(head: Nat, tail: List) extends List
  object Cons {
    def apply =
      (head: Nat) => (tail: List) => new Cons(head, tail)
  }
  case object Nil extends List
  sealed abstract class AbsQueue
  case class Queue(front: List, read: List) extends AbsQueue
  object Queue {
    def apply =
      (front: List) => (read: List) => new Queue(front, read)
  }
  def size(list: List): Nat =
    list match {
      case Nil => 0
      case Cons(_, xs) => 1 + size(xs)
    }
  def concat(l1: List)(l2: List): List =
    l1 match {
      case Nil => l2
      case Cons(x, xs) => Cons(x)(concat(xs)(l2))
    }
  def reverse(l: List): List =
    l match {
      case Nil => Nil
      case Cons(x, xs) => concat(reverse(xs))(Cons(x)(Nil))
    }
  def asList(queue: AbsQueue): List =
    queue match {
      case Queue(front, rear) => concat(front)(reverse(rear))
    }
  def amortizedQueue(front: List)(rear: List): AbsQueue =
    if (size(rear) <= size(front)) Queue(front)(rear)
    else Queue(concat(front)(reverse(rear)))(Nil)
  def enqueue(queue: AbsQueue)(elem: Nat): AbsQueue =
    queue match {
      case Queue(front, rear) => amortizedQueue(front)(Cons(elem)(rear))
    }
  def tail(queue: AbsQueue): Option[AbsQueue] =
    queue match {
      case Queue(Cons(f, fs), rear) => Some(amortizedQueue(fs)(rear))
      case Queue(Nil, _) => None
    }
  def front(queue: AbsQueue): Option[Nat] =
    queue match {
      case Queue(Cons(f, _), _) => Some(f)
      case Queue(Nil, _) => None
    }
}

