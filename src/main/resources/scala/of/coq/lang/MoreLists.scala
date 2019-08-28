package scala.of.coq.lang

object MoreLists {
  type Cons[A] = ::[A]

  object Cons {
    def apply[A](v: A)(tail: List[A]): List[A] = v :: tail
  }

  def length[A](l: List[A]): Int = l.length

  def filter[A](p: A => Boolean, l: List[A]): List[A] = l.filter(p)
  def filter[A] = (p: A => Boolean) => (l: List[A]) => l.filter(p)

  def app[A](l1: List[A], l2: List[A]): List[A] = l1 ++ l2
  def app[A] = (l1: List[A]) => (l2: List[A]) => l1 ++ l2

  def rev[A](l: List[A]): List[A] = l.reverse
  def rev[A] = (l: List[A]) => l.reverse

  def map[A, B](f: A => B, l: List[A]): List[B] = l.map(f)
  def map[A, B] = (f: A => B) => (l: List[A]) => l.map(f)

  def flat_map[A, B](f: A => List[B], l: List[A]): List[B] = l.flatMap(f)
  def flat_map[A, B] = (f: A => List[B]) => (l: List[A]) => l.flatMap(f)

  def fold_left[A, B](op: A => B => A, l: List[B], zero: A): A = l.foldLeft(zero)((x: A, y: B) => op(x)(y))
  def fold_left[A, B] = (op: A => B => A) => (l: List[B]) => (zero: A) => l.foldLeft(zero)((x: A, y: B) => op(x)(y))

  def fold_right[A, B](op: B => A => A, zero: A, l: List[B]): A = l.foldRight(zero)((x: B, y: A) => op(x)(y))
  def fold_right[A, B] = (op: B => A => A) => (zero: A) => (l: List[B]) => l.foldRight(zero)((x: B, y: A) => op(x)(y))
}
