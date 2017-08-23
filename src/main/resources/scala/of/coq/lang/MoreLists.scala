package scala.of.coq.lang

object MoreLists {
  type Cons[A] = ::[A]
  val Cons = ::

  def length[A](l: List[A]): Int = l.length

  def filter[A](p: A => Boolean, l: List[A]): List[A] = l.filter(p)
  def filter[A] = (p: A => Boolean) => (l: List[A]) => l.filter(p)

  def app[A](l1: List[A], l2: List[A]): List[A] = l1 ++ l2
  def app[A] = (l1: List[A]) => (l2: List[A]) => l1 ++ l2

  def map[A, B](f: A => B, l: List[A]): List[B] = l.map(f)
  def map[A, B] = (f: A => B) => (l: List[A]) => l.map(f)

  def flat_map[A, B](f: A => List[B], l: List[A]): List[B] = l.flatMap(f)
  def flat_map[A, B] = (f: A => List[B]) => (l: List[A]) => l.flatMap(f)
}
