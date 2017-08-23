import scala.of.coq.lang._
import Nat._
import MoreLists._
object LengthTailRecForLeon {
  def lenTailrec[A](xs: List[A])(n: BigInt): BigInt =
    xs match {
      case Nil => n
      case Cons(_, ys) => lenTailrec(ys)(1 + n)
    }
}

