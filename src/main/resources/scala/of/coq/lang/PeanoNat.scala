package scala.of.coq.lang

// TODO (Joseph Bakouny): Consider moving such dependencies to a separate Scala project called "scallina-standard-library"
// We can use the same sbt to generate two separate jars: see https://www.scala-sbt.org/0.13/docs/Multi-Project.html
// and https://stackoverflow.com/questions/48540824/how-to-write-a-sbt-file-in-multiple-projects

sealed abstract class Nat {
  def predecessor: Nat = Nat.pred(this)
  def successor: Nat = new S(this)
  def +(that: Nat): Nat = Nat.add(this, that)
  def *(that: Nat): Nat = Nat.mul(this, that)
  def -(that: Nat): Nat = (this, that) match {
    case (S(k), S(l)) => k - l
    case (_, _)       => this
  }
}
case object Zero extends Nat
case class S(n: Nat) extends Nat

object Nat {

  implicit def apply(n: BigInt): Nat =
    if (n <= 0) Zero
    else S(apply(n - 1))

  implicit def apply(n: Int): Nat = apply(BigInt(n))

  implicit def natToBigInt(n: Nat): BigInt = n match {
    case Zero => 0
    case S(m) => 1 + natToBigInt(n)
  }

  // Generated from to Coq.Init.Nat (with manual additions of explicit typing)
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
  //==========================================
}
