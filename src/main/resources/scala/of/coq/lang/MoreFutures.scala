package scala.of.coq.lang
import scala.concurrent._
import scala.concurrent.ExecutionContext.Implicits._
import scala.concurrent.duration._

object MoreFutures {

  private val duration = Duration(100, MILLISECONDS)

  def future[A](expr: => A): Future[A] = Future(expr)
  def getValue[A](fv: Future[A]): A = Await.result(fv, duration)

  def fut_map[A, B](f: A => B, fv: Future[A]): Future[B] = fv.map(f)
  def fut_map[A, B] = (f: A => B) => (fv: Future[A]) => fv.map(f)

  def fut_flat_map[A, B](f: A => Future[B], fv: Future[A]): Future[B] = fv.flatMap(f)
  def fut_flat_map[A, B] = (f: A => Future[B]) => (fv: Future[A]) => fv.flatMap(f)
}
