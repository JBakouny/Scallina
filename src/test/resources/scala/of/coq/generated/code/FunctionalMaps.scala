import scala.of.coq.lang._
import Nat._
import MoreLists._
object FunctionalMaps {
  sealed abstract class id
  case class Id(n: Nat) extends id
  def beq_id(id1: id, id2: id): Boolean =
    (id1, id2) match {
      case (Id(n1), Id(n2)) => n1 == n2
    }
  type total_map[A] = id => A
  def t_empty[A](v: A): total_map[A] = (_ => v)
  def t_update[A](m: total_map[A], x: id, v: A) =
    (x2: id) => if (beq_id(x, x2)) v
    else m(x2)
  def examplemap = t_update(t_update(t_empty(false), Id(1), false), Id(3), true)
  type partial_map[A] = total_map[Option[A]]
  def empty[A](): partial_map[A] = t_empty(None)
  def update[A](m: partial_map[A], x: id, v: A) = t_update(m, x, Some(v))
}

