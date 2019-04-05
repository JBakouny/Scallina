package scala.of.coq.lang

object Bools {
  def negb(b: Boolean): Boolean = !b

  def andb(a: Boolean, b: Boolean): Boolean = a && b
  def andb = (a: Boolean) => (b: Boolean) => a && b

  def orb(a: Boolean, b: Boolean): Boolean = a || b
  def orb = (a: Boolean) => (b: Boolean) => a || b
}
