import scala.of.coq.lang._
import Nat._
import Pairs._
import Bools._
import MoreLists._
import scala.concurrent.Future
import MoreFutures._
object MapsVFA {
  type total_map[A] = Nat => A
  def t_empty[A](v: A): total_map[A] = (_ => v)
  def t_update[A](m: total_map[A])(x: Nat)(v: A): total_map[A] =
    x1 => if (x == x1) v
    else m(x1)
  def examplemap = t_update(t_update(t_empty(false))(1)(false))(3)(true)
}

