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

  // The below function was synthezed from Coq's xorb function using Scallina
  def xorb(b1: Boolean, b2: Boolean): Boolean =
    if (b1) (if (b2) false
    else true)
    else (if (b2) true
    else false)

  def xorb = (b1: Boolean) => (b2: Boolean) =>
    if (b1) (if (b2) false
    else true)
    else (if (b2) true
    else false)

  // The below function was synthezed from Coq's implb function using Scallina
  def implb(b1: Boolean, b2: Boolean): Boolean =
    if (b1) b2
    else true

  def implb = (b1: Boolean) => (b2: Boolean) =>
    if (b1) b2
    else true
}
