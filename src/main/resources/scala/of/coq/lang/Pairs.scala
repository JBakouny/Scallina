package scala.of.coq.lang

object Pairs {
  def fst[A, B](p: (A, B)): A =
    p match {
      case (x, y) => x
    }
  def snd[A, B](p: (A, B)): A =
    p match {
      case (x, y) => x
    }
}
