package scala.of.coq.parsercombinators
import org.scalatest.FunSuite
import scala.of.coq.parsercombinators.compiler.{ScalaOfCoq, Currify}
import scala.of.coq.parsercombinators.parser.CoqParser
class LetScopeCodegenTest extends FunSuite {
 private def generate(source:String):String={
  val parsed=CoqParser(source); assert(parsed.successful,parsed.toString)
  new ScalaOfCoq(parsed.get,Currify,exactNumerics=true,nativeFullConstructors=true).generateScalaCode
 }
 test("qualified globals retain their identity under a lexical alias") {
  val out=generate("Definition value : nat := 7. Definition preserve (value : nat) : nat := let value := value in QualifiedAlias.value.")
  assert(out.contains("QualifiedAlias.value"),out)
 }
 test("nested lets with one source name have distinct target bindings") {
  val out=generate("Definition nested : nat := let value := 1 in let value := 2 in value.")
  val names="val ([a-zA-Z_][a-zA-Z0-9_]*) =".r.findAllMatchIn(out).map(_.group(1)).toList
  assert(names.distinct.size==names.size,out)
 }
 test("later let bindings do not capture earlier parameter references") {
  val out=generate("Definition preserve (value : nat) : nat := let saved := value in let value := 2 in saved.")
  assert(!out.contains("val value = BigInt"),out)
 }
 test("later tuple bindings do not capture earlier parameter references") {
  val out=generate("Definition preserve (value : nat) : nat := let saved := value in let (value, ignored) := (2, 3) in saved.")
  assert(!out.contains("val (value, ignored)"),out)
 }
 test("later pattern lets do not capture earlier parameter references") {
  val out=generate("Definition preserve (value : nat) : nat := let saved := value in let '(value, ignored) := (2, 3) in saved.")
  assert(!out.contains("val (value, ignored)"),out)
 }
 test("earlier global references remain outside later flattened bindings") {
  val out=generate("Definition value : nat := 7. Definition preserve : nat := let saved := value in let value := 2 in saved.")
  assert(!out.contains("val value = BigInt"),out)
 }
}
