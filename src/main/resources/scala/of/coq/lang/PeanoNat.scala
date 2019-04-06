// The Scallina Standard Library
// Joseph Bakouny - 2019
// Peano Nat Implementation

package scala.of.coq.lang

// TODO (Joseph Bakouny): Consider moving such dependencies to a separate Scala project called "scallina-standard-library"
// We can use the same sbt to generate two separate jars: see https://www.scala-sbt.org/0.13/docs/Multi-Project.html
// and https://stackoverflow.com/questions/48540824/how-to-write-a-sbt-file-in-multiple-projects

sealed abstract class Nat {
  def predecessor: Nat = Nat.pred(this)
  def successor: Nat = new S(this)
  def +(that: Nat): Nat = Nat.add(this)(that)
  def *(that: Nat): Nat = Nat.mul(this)(that)
  def -(that: Nat): Nat = Nat.sub(this)(that)
}
case object Zero extends Nat
case class S(n: Nat) extends Nat

object CurriedNat {

}

object Nat {

  implicit def apply(n: BigInt): Nat =
    if (n < 0) throw new IllegalArgumentException("Cannot convert negative number " + n + " to a natural number")
    else if (n == 0) Zero
    else S(apply(n - 1))

  implicit def apply(n: Int): Nat = apply(BigInt(n))

  implicit def natToBigInt(n: Nat): BigInt = n match {
    case Zero => 0
    case S(m) => 1 + natToBigInt(n)
  }

  import Bools._
  import Pairs._

  // Translated from Coq.Init.Nat using the Scallina prototype
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
  def double(n: Nat): Nat = add(n)(n)
  def mul(n: Nat)(m: Nat): Nat =
    n match {
      case Zero => Zero
      case S(p) => add(m)(mul(p)(m))
    }
  def sub(n: Nat)(m: Nat): Nat =
    (n, m) match {
      case (S(k), S(l)) => sub(k)(l)
      case (_, _)       => n
    }
  def eqb(n: Nat)(m: Nat): Boolean =
    (n, m) match {
      case (Zero, Zero)   => true
      case (Zero, S(_))   => false
      case (S(_), Zero)   => false
      case (S(n1), S(m1)) => eqb(n1)(m1)
    }
  def leb(n: Nat)(m: Nat): Boolean =
    (n, m) match {
      case (Zero, _)      => true
      case (_, Zero)      => false
      case (S(n1), S(m1)) => leb(n1)(m1)
    }
  def ltb(n: Nat)(m: Nat) = leb(S(n))(m)
  def compare(n: Nat)(m: Nat): comparison =
    (n, m) match {
      case (Zero, Zero)   => Eq
      case (Zero, S(_))   => Lt
      case (S(_), Zero)   => Gt
      case (S(n1), S(m1)) => compare(n1)(m1)
    }
  def max(n: Nat)(m: Nat): Nat =
    (n, m) match {
      case (Zero, _)      => m
      case (S(n1), Zero)  => n
      case (S(n1), S(m1)) => S(max(n1)(m1))
    }
  def min(n: Nat)(m: Nat): Nat =
    (n, m) match {
      case (Zero, _)      => Zero
      case (S(n1), Zero)  => Zero
      case (S(n1), S(m1)) => S(min(n1)(m1))
    }
  def even(n: Nat): Boolean =
    n match {
      case Zero     => true
      case S(Zero)  => false
      case S(S(n1)) => even(n1)
    }
  def odd(n: Nat): Boolean = negb(even(n))
  def pow(n: Nat)(m: Nat): Nat =
    m match {
      case Zero => S(Zero)
      case S(m) => mul(n)(pow(n)(m))
    }
  def tail_add(n: Nat)(m: Nat): Nat =
    n match {
      case Zero => m
      case S(n) => tail_add(n)(S(m))
    }
  def tail_addmul(r: Nat)(n: Nat)(m: Nat): Nat =
    n match {
      case Zero => r
      case S(n) => tail_addmul(tail_add(m)(r))(n)(m)
    }
  def divmod(x: Nat)(y: Nat)(q: Nat)(u: Nat): (Nat, Nat) =
    x match {
      case Zero => (q, u)
      case S(x1) => u match {
        case Zero  => divmod(x1)(y)(S(q))(y)
        case S(u1) => divmod(x1)(y)(q)(u1)
      }
    }
  def div(x: Nat)(y: Nat): Nat =
    y match {
      case Zero  => y
      case S(y1) => fst(divmod(x)(y1)(Zero)(y1))
    }
  def modulo(x: Nat)(y: Nat) =
    y match {
      case Zero  => y
      case S(y1) => sub(y1)(snd(divmod(x)(y1)(Zero)(y1)))
    }
  def gcd(a: Nat)(b: Nat): Nat =
    a match {
      case Zero  => b
      case S(a1) => gcd(modulo(b)(S(a1)))(S(a1))
    }
  def square(n: Nat): Nat = mul(n)(n)
  def sqrt_iter(k: Nat)(p: Nat)(q: Nat)(r: Nat): Nat =
    k match {
      case Zero => p
      case S(k1) => r match {
        case Zero  => sqrt_iter(k1)(S(p))(S(S(q)))(S(S(q)))
        case S(r1) => sqrt_iter(k1)(p)(q)(r1)
      }
    }
  def sqrt(n: Nat): Nat = sqrt_iter(n)(Zero)(Zero)(Zero)
  def log2_iter(k: Nat)(p: Nat)(q: Nat)(r: Nat): Nat =
    k match {
      case Zero => p
      case S(k1) => r match {
        case Zero  => log2_iter(k1)(S(p))(S(q))(q)
        case S(r1) => log2_iter(k1)(p)(S(q))(r1)
      }
    }
  def log2(n: Nat): Nat = log2_iter(pred(n))(Zero)(S(Zero))(Zero)
  def iter[A](n: Nat)(f: A => A)(x: A): A =
    n match {
      case Zero  => x
      case S(n0) => f(iter(n0)(f)(x))
    }
  def div2(n: Nat): Nat =
    n match {
      case Zero     => Zero
      case S(Zero)  => Zero
      case S(S(n1)) => S(div2(n1))
    }
  def testbit(a: Nat)(n: Nat): Boolean =
    n match {
      case Zero => odd(a)
      case S(n) => testbit(div2(a))(n)
    }
  def shiftl(a: Nat)(n: Nat): Nat =
    n match {
      case Zero  => a
      case S(n0) => double(shiftl(a)(n0))
    }
  def shiftr(a: Nat)(n: Nat): Nat =
    n match {
      case Zero  => a
      case S(n0) => div2(shiftr(a)(n0))
    }
  def bitwise(op: Boolean => Boolean => Boolean)(n: Nat)(a: Nat)(b: Nat): Nat =
    n match {
      case Zero => Zero
      case S(n1) => add(if (op(odd(a))(odd(b))) S(Zero)
      else Zero)(mul(S(S(Zero)))(bitwise(op)(n1)(div2(a))(div2(b))))
    }
  def land(a: Nat)(b: Nat): Nat = bitwise(andb)(a)(a)(b)
  def lor(a: Nat)(b: Nat): Nat = bitwise(orb)(max(a)(b))(a)(b)
  def ldiff(a: Nat)(b: Nat): Nat = bitwise(b => b1 => andb(b)(negb(b1)))(a)(a)(b)
  def lxor(a: Nat)(b: Nat): Nat = bitwise(xorb)(max(a)(b))(a)(b)
  //==========================================

  // Tupled equivalents of the functions that were generated above
  def add: (Nat, Nat) => Nat = (n: Nat, m: Nat) => add(n)(m)
  def mul: (Nat, Nat) => Nat = (n: Nat, m: Nat) => add(n)(m)
  def sub: (Nat, Nat) => Nat = (n: Nat, m: Nat) => add(n)(m)
  def eqb: (Nat, Nat) => Boolean = (n: Nat, m: Nat) => eqb(n)(m)
  def leb: (Nat, Nat) => Boolean = (n: Nat, m: Nat) => leb(n)(m)
  def ltb: (Nat, Nat) => Boolean = (n: Nat, m: Nat) => ltb(n)(m)
  def compare: (Nat, Nat) => comparison = (n: Nat, m: Nat) => compare(n)(m)
  def max: (Nat, Nat) => Nat = (n: Nat, m: Nat) => max(n)(m)
  def min: (Nat, Nat) => Nat = (n: Nat, m: Nat) => min(n)(m)
  def pow: (Nat, Nat) => Nat = (n: Nat, m: Nat) => pow(n)(m)
  def tail_add: (Nat, Nat) => Nat = (n: Nat, m: Nat) => tail_add(n)(m)
  def tail_addmul: (Nat, Nat, Nat) => Nat = (r: Nat, n: Nat, m: Nat) => tail_addmul(r)(n)(m)
  def divmod: (Nat, Nat, Nat, Nat) => (Nat, Nat) = (x: Nat, y: Nat, q: Nat, u: Nat) => divmod(x)(y)(q)(u)
  def div: (Nat, Nat) => Nat = (x: Nat, y: Nat) => div(x)(y)
  def modulo: (Nat, Nat) => Nat = (x: Nat, y: Nat) => modulo(x)(y)
  def gcd: (Nat, Nat) => Nat = (a: Nat, b: Nat) => gcd(a)(b)
  def sqrt_iter: (Nat, Nat, Nat, Nat) => Nat = (k: Nat, p: Nat, q: Nat, r: Nat) => sqrt_iter(k)(p)(q)(r)
  def log2_iter: (Nat, Nat, Nat, Nat) => Nat = (k: Nat, p: Nat, q: Nat, r: Nat) => log2_iter(k)(p)(q)(r)
  def iter[A]: (Nat, A => A, A) => A = (n: Nat, f: A => A, x: A) => iter(n)(f)(x)
  def testbit: (Nat, Nat) => Boolean = (a: Nat, n: Nat) => testbit(a)(n)
  def shiftl: (Nat, Nat) => Nat = (a: Nat, n: Nat) => shiftl(a)(n)
  def shiftr: (Nat, Nat) => Nat = (a: Nat, n: Nat) => shiftr(a)(n)
  def bitwise: (Boolean => Boolean => Boolean, Nat, Nat, Nat) => Nat =
    (op: Boolean => Boolean => Boolean, n: Nat, a: Nat, b: Nat) => bitwise(op)(n)(a)(b)
  def land: (Nat, Nat) => Nat = (a: Nat, b: Nat) => land(a)(b)
  def lor: (Nat, Nat) => Nat = (a: Nat, b: Nat) => lor(a)(b)
  def ldiff: (Nat, Nat) => Nat = (a: Nat, b: Nat) => ldiff(a)(b)
  def lxor: (Nat, Nat) => Nat = (a: Nat, b: Nat) => lxor(a)(b)
}
