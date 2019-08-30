import scala.of.coq.lang._
import Nat._
import Pairs._
import Bools._
import MoreLists._
import scala.concurrent.Future
import MoreFutures._
object ListQueueParam {
  trait Queue {
    type t
    def empty: t
    def push: Nat => t => t
    def pop: t => Option[(Nat, t)]
  }
  def sumElems(Q: Queue)(q: Option[Q.t]): Option[Q.t] =
    q match {
      case Some(q1) => Q.pop(q1) match {
        case Some((x, q2)) => Q.pop(q2) match {
          case Some((y, q3)) => Some(Q.push(x + y)(q3))
          case None => None
        }
        case None => None
      }
      case None => None
    }
  def loop[P](n: Nat)(op: Nat => P => P)(x: P): P =
    n match {
      case Zero => x
      case S(n0) => op(n0)(loop(n0)(op)(x))
    }
  def program(Q: Queue)(n: Nat): Option[Nat] = {
    val q = loop(S(n))(Q.push)(Q.empty)
    val q0 = loop(n)(_ => (q0: Option[Q.t]) => sumElems(Q)(q0))(Some(q))
    q0 match {
      case Some(q1) => Q.pop(q1) match {
        case Some((x, q2)) => Some(x)
        case None => None
      }
      case None => None
    }
  }
  object ListQueue extends Queue {
    type t = List[Nat]
    def empty: t = Nil
    def push: Nat => t => t = x => l => x :: l
    def pop: t => Option[(Nat, t)] = l => rev(l) match {
      case Nil => None
      case hd :: tl => Some((hd, rev(tl)))
    }
  }
  object DListQueue extends Queue {
    type t = (List[Nat], List[Nat])
    def empty: t = (Nil, Nil)
    def push: Nat => t => t = x => { l =>
      val (back, front) = l
      (x :: back, front)
    }
    def pop: t => Option[(Nat, t)] = { l =>
      val (back, front) = l
      front match {
        case Nil => rev(back) match {
          case Nil => None
          case hd :: tl => Some((hd, (Nil, tl)))
        }
        case hd :: tl => Some((hd, (back, tl)))
      }
    }
  }
}

