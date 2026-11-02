package scala.of.coq.exact

/** Structural target for the standard Rocq Decimal.uint inductive. */
object Decimal {
  sealed trait uint

  case object Nil extends uint
  final case class D0(tail: uint) extends uint
  final case class D1(tail: uint) extends uint
  final case class D2(tail: uint) extends uint
  final case class D3(tail: uint) extends uint
  final case class D4(tail: uint) extends uint
  final case class D5(tail: uint) extends uint
  final case class D6(tail: uint) extends uint
  final case class D7(tail: uint) extends uint
  final case class D8(tail: uint) extends uint
  final case class D9(tail: uint) extends uint
}
