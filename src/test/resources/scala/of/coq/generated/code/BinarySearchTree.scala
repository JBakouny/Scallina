import scala.of.coq.lang._
import Nat._
import Pairs._
import MoreLists._
object BinarySearchTree {
  sealed abstract class tree[+V]
  case class E[V](default: V) extends tree[V]
  case class T[V](l: tree[V], key: Nat, value: V, r: tree[V]) extends tree[V]
  object T {
    def apply[V] =
      (l: tree[V]) => (key: Nat) => (value: V) => (r: tree[V]) => new T(l, key, value, r)
  }
  def empty_tree[V](default: V) = E(default)
  def lookup[V](x: Nat)(t: tree[V]): V =
    t match {
      case E(default) => default
      case T(tl, k, v, tr) => if (x < k) lookup(x)(tl)
      else if (k < x) lookup(x)(tr)
      else v
    }
  def insert[V](x: Nat)(v: V)(s: tree[V]): tree[V] =
    s match {
      case E(dflt) => T(E(dflt))(x)(v)(E(dflt))
      case T(a, y, v2, b) => if (x < y) T(insert(x)(v)(a))(y)(v2)(b)
      else if (y < x) T(a)(y)(v2)(insert(x)(v)(b))
      else T(a)(x)(v)(b)
    }
  def elements_aux[V](s: tree[V])(base: List[(Nat, V)]): List[(Nat, V)] =
    s match {
      case E(_) => base
      case T(a, k, v, b) => elements_aux(a)((k, v) :: elements_aux(b)(base))
    }
  def elements[V](s: tree[V]): List[(Nat, V)] = elements_aux(s)(Nil)
}

