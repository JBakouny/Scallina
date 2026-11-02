package scala.of.coq.exact

/** Binary positive constructor boundary for exact-numerics output. */
object ExactPositive {
  val xH: BigInt = BigInt(1)

  object xO {
    def apply(rest: BigInt): BigInt = ExactN.pos(rest) * 2
    def unapply(value: BigInt): Option[BigInt] =
      if (value > 1 && value % 2 == 0) Some(value / 2) else None
  }

  object xI {
    def apply(rest: BigInt): BigInt = ExactN.pos(rest) * 2 + 1
    def unapply(value: BigInt): Option[BigInt] =
      if (value > 1 && value % 2 == 1) Some((value - 1) / 2) else None
  }
}
