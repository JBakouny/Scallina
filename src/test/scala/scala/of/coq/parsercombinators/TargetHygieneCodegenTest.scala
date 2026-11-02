package scala.of.coq.parsercombinators
import org.scalatest.FunSuite
import scala.of.coq.parsercombinators.compiler.{ScalaOfCoq,Currify}
import scala.of.coq.parsercombinators.parser.CoqParser
class TargetHygieneCodegenTest extends FunSuite {
 private def generate(source:String):String={val parsed=CoqParser(source);assert(parsed.successful,parsed.toString);new ScalaOfCoq(parsed.get,Currify,exactNumerics=true,nativeFullConstructors=true).generateScalaCode}
 test("qualified user members retain lowercase standard-like spellings") {
  val out=generate("Definition cons (n : nat) : nat := n. Definition preserve : nat := QualifiedCons.cons 5.")
  assert(out.contains("QualifiedCons.cons"),out)
 }
 test("later lexical bindings cannot capture earlier qualified roots") {
  val out=generate("Definition value : nat := 7. Definition preserve : nat := let saved := QualifiedRoot.value in let QualifiedRoot := 2 in saved.")
  assert(!out.contains("val QualifiedRoot ="),out)
 }
 test("later lexical bindings cannot capture generated runtime roots") {
  val out=generate("Definition preserve : nat := let saved := S 5 in let scala := 2 in saved.")
  assert(!out.contains("val scala ="),out)
 }
 test("runtime-root names stay hygienic when their body uses a primitive") {
  val out=generate("Definition preserve : nat := let scala := 2 in S 5.")
  assert(!out.contains("val scala ="),out)
 }
 test("later tuple patterns cannot capture qualified roots") {
  val out=generate("Definition value : nat := 7. Definition preserve : nat := let saved := QualifiedRoot.value in let (QualifiedRoot, ignored) := (2, 3) in saved.")
  assert(!out.contains("val (QualifiedRoot,"),out)
 }
 test("later quoted patterns cannot capture generated roots") {
  val out=generate("Definition preserve : nat := let saved := S 5 in let '(scala, ignored) := (2, 3) in saved.")
  assert(!out.contains("val (scala,"),out)
 }
 test("fresh let identifiers avoid actual source declarations") {
  val out=generate("Definition scallinaLet_value : nat := 7. Definition preserve : nat := let value := 2 in scallinaLet_value.")
  assert(!out.contains("val scallinaLet_value ="),out)
 }
}
