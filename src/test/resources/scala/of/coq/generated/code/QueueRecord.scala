import scala.of.coq.lang._
import Nat._
import MoreLists._
object QueueRecord {
  trait Queue {
    type T
    def empty: T
    def push: Nat => T => T
    def pop: T => Option[(Nat, T)]
  }
  def Build_Queue[Queue_T](Queue_empty: Queue_T)(Queue_push: Nat => Queue_T => Queue_T)(Queue_pop: Queue_T => Option[(Nat, Queue_T)]): Queue = {
    new Queue {
      type T = Queue_T
      def empty = Queue_empty
      def push = Queue_push
      def pop = Queue_pop
    }
  }
  def ListQueue = Build_Queue[List[Nat]](Nil)((x: Nat) => (l: List[Nat]) => x :: l)(l => rev(l) match {
    case Nil      => None
    case hd :: tl => Some((hd, rev(tl)))
  })
  def DListQueue = Build_Queue[(List[Nat], List[Nat])]((Nil, Nil))((x: Nat) => { (l: (List[Nat], List[Nat])) =>
      val (back, front) = l
      (x :: back, front)
    })({ l =>
      val (back, front) = l
      front match {
        case Nil => rev(back) match {
          case Nil => None
          case hd :: tl => Some((hd, (Nil, tl)))
        }
        case hd :: tl => Some((hd, (back, tl)))
      }
    })
  def insertElems(Q: Queue)(q: Q.T)(n: Nat): Q.T =
    n match {
      case Zero => q
      case S(m) => Q.push(n)(insertElems(Q)(q)(m))
    }
  def createQueue(Q: Queue)(n: Nat): Q.T = insertElems(Q)(Q.empty)(n)
  def createListQueue(n: Nat) = createQueue(ListQueue)(n)
  def createDListQueue(n: Nat) = createQueue(DListQueue)(n)
}
