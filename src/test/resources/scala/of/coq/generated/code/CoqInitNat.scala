import scala.of.coq.lang._
import Nat._
import Pairs._
import MoreLists._
import scala.concurrent.Future
import MoreFutures._
object CoqInitNat {
  sealed abstract class Nat
  case object Zero extends Nat
  case class S(n: Nat) extends Nat
  def pred(n: Nat): Nat =
    n match {
      case Zero => n
      case S(u) => u
    }
  def add(n: Nat)(m: Nat): Nat =
    n match {
      case Zero => m
      case S(p) => S(add(p)(m))
    }
  def mul(n: Nat)(m: Nat): Nat =
    n match {
      case Zero => Zero
      case S(p) => add(m)(mul(p)(m))
    }
  def sub(n: Nat)(m: Nat): Nat =
    (n, m) match {
      case (S(k), S(l)) => sub(k)(l)
      case (_, _) => n
    }
}

