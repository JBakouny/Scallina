package scala.of.coq.lang

object Bools {
  sealed abstract class comparison
  case object Eq extends comparison
  case object Lt extends comparison
  case object Gt extends comparison

  def negb(b: Boolean): Boolean = !b

  def andb(a: Boolean, b: Boolean): Boolean = a && b
  def andb = (a: Boolean) => (b: Boolean) => a && b

  def orb(a: Boolean, b: Boolean): Boolean = a || b
  def orb = (a: Boolean) => (b: Boolean) => a || b
}
