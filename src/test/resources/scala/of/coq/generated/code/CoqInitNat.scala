import scala.of.coq.lang._
import Nat._
import MoreLists._
object CoqInitNat {
  def pred(n: Nat): Nat =
    n match {
      case Zero => n
      case S(u) => u
    }
  def add(n: Nat, m: Nat): Nat =
    n match {
      case Zero => m
      case S(p) => S(p + m)
    }
  def mul(n: Nat, m: Nat): Nat =
    n match {
      case Zero => 0
      case S(p) => m + (p * m)
    }
}

