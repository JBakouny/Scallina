import scala.of.coq.lang._
import Nat._
import Pairs._
import MoreLists._
object RedBlackTree {
  sealed abstract class color
  case object Red extends color
  case object Black extends color
  sealed abstract class tree[V]
  case class E[V](default: V) extends tree[V]
  case class T[V](c: color, l: tree[V], key: BigInt, value: V, r: tree[V]) extends tree[V]
  object T {
    def apply[V] =
      (c: color) => (l: tree[V]) => (key: BigInt) => (value: V) => (r: tree[V]) => new T(c, l, key, value, r)
  }
  def empty_tree[V](default: V) = E(default)
  def lookup[V](x: BigInt)(t: tree[V]): V =
    t match {
      case E(default) => default
      case T(_, tl, k, v, tr) => if ((x < k)) lookup(x)(tl)
      else if ((k < x)) lookup(x)(tr)
      else v
    }
  def balance[V](rb: color)(t1: tree[V])(k: BigInt)(vk: V)(t2: tree[V]): tree[V] =
    rb match {
      case Red => T(Red)(t1)(k)(vk)(t2)
      case _ => t1 match {
        case T(Red, T(Red, a, x, vx, b), y, vy, c) => T(Red)(T(Black)(a)(x)(vx)(b))(y)(vy)(T(Black)(c)(k)(vk)(t2))
        case T(Red, a, x, vx, T(Red, b, y, vy, c)) => T(Red)(T(Black)(a)(x)(vx)(b))(y)(vy)(T(Black)(c)(k)(vk)(t2))
        case a => t2 match {
          case T(Red, T(Red, b, y, vy, c), z, vz, d) => T(Red)(T(Black)(t1)(k)(vk)(b))(y)(vy)(T(Black)(c)(z)(vz)(d))
          case T(Red, b, y, vy, T(Red, c, z, vz, d)) => T(Red)(T(Black)(t1)(k)(vk)(b))(y)(vy)(T(Black)(c)(z)(vz)(d))
          case _ => T(Black)(t1)(k)(vk)(t2)
        }
      }
    }
  def makeBlack[V](t: tree[V]): tree[V] =
    t match {
      case E(dflt) => E(dflt)
      case T(_, a, x, vx, b) => T(Black)(a)(x)(vx)(b)
    }
  def ins[V](x: BigInt)(vx: V)(s: tree[V]): tree[V] =
    s match {
      case E(dflt) => T(Red)(E(dflt))(x)(vx)(E(dflt))
      case T(c, a, y, vy, b) => if ((x < y)) balance(c)(ins(x)(vx)(a))(y)(vy)(b)
      else if ((y < x)) balance(c)(a)(y)(vy)(ins(x)(vx)(b))
      else T(c)(a)(x)(vx)(b)
    }
  def insert[V](x: BigInt)(vx: V)(s: tree[V]): tree[V] = makeBlack(ins(x)(vx)(s))
}

