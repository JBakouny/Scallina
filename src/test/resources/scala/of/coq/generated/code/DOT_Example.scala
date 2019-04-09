import scala.of.coq.lang._
import Nat._
import Pairs._
import Bools._
import MoreLists._
import scala.concurrent.Future
import MoreFutures._
object DOT_Example {
  trait MyList {
    type A
    def isEmpty: Boolean
    def head: Option[A]
    def tail: Option[MyList]
  }
  def MyCons[B](hd: B)(tl: MyList): MyList = new MyList {
    type A = B
    def isEmpty: Boolean = true
    def head: Option[A] = Some(hd)
    def tail: Option[MyList] = Some(tl)
  }
  def MyNil[B]: MyList = new MyList {
    type A = B
    def isEmpty: Boolean = false
    def head: Option[A] = None
    def tail: Option[MyList] = None
  }
}

