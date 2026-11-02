package scala.of.coq.exact

/** Representation boundary for Rocq N and positive values in exact-numerics output. */
object ExactN {
  val N0: BigInt = BigInt(0)

  object Npos {
    def apply(value: BigInt): BigInt = pos(value)

    def unapply(value: BigInt): Option[BigInt] =
      if (value > 0) Some(value) else None
  }

  def ofNat(value: BigInt): BigInt = {
    require(value >= 0, "Rocq nat cannot be negative")
    value
  }

  def toNat(value: BigInt): BigInt = {
    require(value >= 0, "Rocq N cannot be negative")
    value
  }

  def size(value: BigInt): BigInt = BigInt(toNat(value).bitLength)

  def toUint(value: BigInt): Decimal.uint = {
    require(value >= 0, "Rocq N cannot be negative")
    value.toString.foldRight[Decimal.uint](Decimal.Nil) {
      case ('0', tail) => Decimal.D0(tail)
      case ('1', tail) => Decimal.D1(tail)
      case ('2', tail) => Decimal.D2(tail)
      case ('3', tail) => Decimal.D3(tail)
      case ('4', tail) => Decimal.D4(tail)
      case ('5', tail) => Decimal.D5(tail)
      case ('6', tail) => Decimal.D6(tail)
      case ('7', tail) => Decimal.D7(tail)
      case ('8', tail) => Decimal.D8(tail)
      case ('9', tail) => Decimal.D9(tail)
      case (digit, _) => throw new IllegalStateException(s"unexpected decimal digit: $digit")
    }
  }

  def pos(value: BigInt): BigInt = {
    require(value > 0, "Rocq positive must be greater than zero")
    value
  }
}
