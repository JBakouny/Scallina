import scala.of.coq.lang._
import Nat._
import Pairs._
import Bools._
import MoreLists._
import scala.concurrent.Future
import MoreFutures._
object LengthTailRecForLeon {
  def lenTailrec[A](xs: List[A])(n: BigInt): BigInt =
    xs match {
      case Nil => n
      case Cons(_, ys) => lenTailrec(ys)(1 + n)
    }
}

