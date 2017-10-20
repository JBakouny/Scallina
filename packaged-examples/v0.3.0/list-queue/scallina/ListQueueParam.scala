import scala.of.coq.lang._
import Nat._
import Pairs._
import MoreLists._
object ListQueueParam {
  trait Queue {
    type t
    def empty: t
    def push: Nat => t => t
    def pop: t => Option[(Nat, t)]
  }
  def Build_Queue[t](empty: t)(push: Nat => t => t)(pop: t => Option[(Nat, t)]): Queue = {
    type Queue_t = t
    def Queue_empty = empty
    def Queue_push = push
    def Queue_pop = pop
    new Queue {
      type t = Queue_t
      def empty: t = Queue_empty
      def push: Nat => t => t = Queue_push
      def pop: t => Option[(Nat, t)] = Queue_pop
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
  def bind_option[A, B](x: Option[A])(f: A => Option[B]): Option[B] =
    x match {
      case Some(x) => f(x)
      case None => None
    }
  def bind_option2[A, B, C](x: Option[(A, B)])(f: A => B => Option[C]): Option[C] = bind_option(x)({ (yz: (A, B)) =>
    val (y, z) = yz
    f(y)(z)
  })
  def option_map[A, B](o: Option[A])(f: A => B): Option[B] =
    o match {
      case Some(a) => Some(f(a))
      case None => None
    }
  def nat_rect[P](op: Nat => P => P)(n: Nat)(x: P): P =
    n match {
      case Zero => x
      case S(n0) => op(n0)(nat_rect(op)(n0)(x))
    }
  def sumElems(Q: Queue)(q0: Option[Q.t]): Option[Q.t] = bind_option(q0)({ (q1: Q.t) =>
    val x_q1 = Q.pop(q1)
    bind_option2(x_q1)((x: Nat) => { (q2: Q.t) =>
      val y_q3 = Q.pop(q2)
      bind_option2(y_q3)((y: Nat) => { (q3: Q.t) =>
        val sum = x + y
        Some(Q.push(sum)(q3))
      })
    })
  })
  def program(Q: Queue)(n: Nat): Option[Nat] = {
    val q: Q.t = nat_rect(Q.push)(S(n))(Q.empty)
    val q0: Option[Q.t] = nat_rect(_ => (q0: Option[Q.t]) => sumElems(Q)(q0))(n)(Some(q))
    bind_option(q0)((q1: Q.t) => option_map(Q.pop(q1))(fst))
  }
}

