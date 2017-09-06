import scala.of.coq.lang._
import Nat._
import MoreLists._
object QueueRecordAnotherAlternateSyntax {
  trait Queue {
    type T
    def push: Nat => T => T
    def pop: T => Option[(Nat, T)]
    def empty: T
  }
  def Build_Queue[T](push: Nat => T => T)(pop: T => Option[(Nat, T)])(empty: T): Queue = {
    type Queue_T = T
    def Queue_push = push
    def Queue_pop = pop
    def Queue_empty = empty
    new Queue {
      type T = Queue_T
      def push: Nat => T => T = Queue_push
      def pop: T => Option[(Nat, T)] = Queue_pop
      def empty: T = Queue_empty
    }
  }
  def ListQueue = Build_Queue((x: Nat) => (l: List[Nat]) => x :: l)(l => rev(l) match {
    case Nil => None
    case hd :: tl => Some((hd, rev(tl)))
  })(Nil)
  def DListQueue = Build_Queue((x: Nat) => { (l: (List[Nat], List[Nat])) =>
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
  })((Nil, Nil))
  def insertElems(Q: Queue)(q: Q.T)(n: Nat): Q.T =
    n match {
      case Zero => q
      case S(m) => Q.push(n)(insertElems(Q)(q)(m))
    }
  def createQueue(Q: Queue)(n: Nat): Q.T = insertElems(Q)(Q.empty)(n)
  def createListQueue(n: Nat) = createQueue(ListQueue)(n)
  def createDListQueue(n: Nat) = createQueue(DListQueue)(n)
}

