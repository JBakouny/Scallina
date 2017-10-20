import scala.of.coq.lang._
import Nat._
import Pairs._
import MoreLists._
object TestListFunctions {
  def f(x: Nat): Nat = x * 3
  def l: List[Nat] = 7 :: Nil
  def testMap = map(f)(l)
  def g(x: Nat): Boolean =
    if (x < 2) true
    else false
  def testFilter = filter(g)(l)
  def f2(x: Nat): List[Nat] = (x * 2) :: ((x * 3) :: Nil)
  def testFlatMap = flat_map(f2)(l)
}

