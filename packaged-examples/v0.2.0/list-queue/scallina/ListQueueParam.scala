import scala.of.coq.lang._
import Nat._
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
  def bind_option[A, B](f: A => Option[B])(x: Option[A]): Option[B] =
    x match {
      case Some(x) => f(x)
      case None => None
    }
  def bind_option2[A, B, C](f: A => B => Option[C])(x: Option[(A, B)]): Option[C] = bind_option({ (yz: (A, B)) =>
    val (y, z) = yz
    f(y)(z)
  })(x)
  def nat_rect[P](f: P)(f0: Nat => P => P)(n: Nat): P =
    n match {
      case Zero => f
      case S(n0) => f0(n0)(nat_rect(f)(f0)(n0))
    }
  def option_map[A, B](f: A => B)(o: Option[A]): Option[B] =
    o match {
      case Some(a) => Some(f(a))
      case None => None
    }
  def program(Q: Queue)(n: Nat) = {
    val q = nat_rect(Q.empty)(Q.push)(S(n))
    {
      val q0 = nat_rect(Some(q))(_ => (q0: Option[Q.t]) => bind_option((q1: Q.t) => bind_option2((x: Nat) => (q2: Q.t) => bind_option2((y: Nat) => (q3: Q.t) => Some(Q.push(x + y)(q3)))(Q.pop(q2)))(Q.pop(q1)))(q0))(n)
      bind_option((q1: Q.t) => option_map(fst)(Q.pop(q1)))(q0)
    }
  }
}

