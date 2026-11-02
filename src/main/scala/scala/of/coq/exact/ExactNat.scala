package scala.of.coq.exact

/** Numeric representation of Rocq's O and S for exact-numerics output. */
object ExactNat {
  val O: BigInt = BigInt(0)

  object S {
    def apply(predecessor: BigInt): BigInt = {
      require(predecessor >= O, "natural predecessor must be nonnegative")
      predecessor + 1
    }

    def unapply(value: BigInt): Option[BigInt] =
      if (value > O) Some(value - 1) else None
  }
}
