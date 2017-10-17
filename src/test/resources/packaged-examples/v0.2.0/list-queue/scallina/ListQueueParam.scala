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
}

