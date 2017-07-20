import scala.of.coq.lang._
import Nat._
import MoreLists._
object LengthTailRec {
  def lenTailrec[A](xs: List[A], n: Nat): Nat =
    xs match {
      case Nil => n
      case _ :: ys => lenTailrec(ys, 1 + n)
    }
}

