package scala.of.coq.exact

/** Exact natural-count boundaries for Rocq List operations. */
object ExactList {
  private def natural(count: BigInt): BigInt = {
    require(count >= 0, "Rocq nat cannot be negative")
    count
  }

  def repeat[A](value: A)(count: BigInt): List[A] = {
    val n = natural(count)
    require(n <= BigInt(Int.MaxValue), "Rocq list count exceeds Scala List capacity")
    List.fill(n.toInt)(value)
  }

  def firstn[A](count: BigInt)(values: List[A]): List[A] = {
    val n = natural(count)
    if (n >= values.length) values else values.take(n.toInt)
  }

  def skipn[A](count: BigInt)(values: List[A]): List[A] = {
    val n = natural(count)
    if (n >= values.length) Nil else values.drop(n.toInt)
  }
}
