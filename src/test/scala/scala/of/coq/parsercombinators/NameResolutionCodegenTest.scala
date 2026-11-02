package scala.of.coq.parsercombinators
import org.scalatest.FunSuite
import scala.of.coq.parsercombinators.compiler.{ScalaOfCoq, Currify}
import scala.of.coq.parsercombinators.parser.CoqParser
class NameResolutionCodegenTest extends FunSuite {
 private def generate(source:String,exact:Boolean=true):String={
  val parsed=CoqParser(source);assert(parsed.successful,parsed.toString)
  new ScalaOfCoq(parsed.get,Currify,exactNumerics=exact,nativeFullConstructors=exact).generateScalaCode
 }
 test("future value definitions do not capture an earlier standard constructor") {
  for(exact<-List(false,true)){
   val out=generate("""From Stdlib Require Import List.
    Definition singleton (n : nat) : list nat := cons n nil.
    Definition cons (n : nat) : nat := n.""",exact)
   assert(out.contains("Cons(n)(Nil)"),out)
  }
 }
 test("a value parameter cannot capture constructors in a natural pattern") {
  val out=generate("Definition shadow (S : nat -> nat) (n : nat) : nat := match n with | O => 0 | S p => S p end.")
  assert(out.contains("case scala.of.coq.exact.ExactNat.S(p)"),out)
  assert(out.contains("S(p)"),out)
 }
 test("proposition type names are legal value binders in patterns") {
  val out=generate("Definition identity (n : nat) : nat := match n with | True => True end.")
  assert(!out.contains("case true"),out);assert(!out.contains("=> true"),out)
  assert(out.contains("case scallinaPatternTrue => scallinaPatternTrue"),out)
 }
 test("uppercase pattern aliases avoid declared source names") {
  val out=generate("""Definition scallinaPatternTrue (n : nat) : nat := n.
    Definition identity (n : nat) : nat := match n with | True => True end.""")
  assert(out.contains("case scallinaPatternTrue1 => scallinaPatternTrue1"),out)
 }
 test("upper pattern names and lexical aliases restore before sibling branches") {
  val out=generate("""Definition choose (n : option nat) (fallback : nat) : nat :=
   match n with | Some True => True | None => fallback end.""")
  assert(out.contains("Some(scallinaPatternTrue)"),out)
  assert(out.contains("case None => fallback"),out)
 }

 test("future constructor declarations do not change an earlier natural pattern") {
  val out=generate("""Definition before (n : nat) : nat := match n with | O => 0 | S p => p end.
    Inductive later := S.""")
  assert(out.contains("case scala.of.coq.exact.ExactNat.S(p)"),out)
 }
 test("ambiguous uppercase external patterns require exact declaration context") {
  val error=intercept[IllegalStateException] { generate("Definition choose (n : tree) := match n with | E => 0 end.") }
  assert(error.getMessage.contains("declaration context"))
 }

 test("actual constructor metadata precedes proposition-name literal rewrites") {
  val out=generate("""Inductive proposition_names := True | False.
    Definition choose (n : proposition_names) : bool := match n with | True => true | False => false end.""")
  assert(out.contains("case True => true"),out)
  assert(out.contains("case False => false"),out)
 }

 test("nonrecursive let bindings do not capture their own initializer") {
  val out=generate("Definition identity (value : nat) : nat := let value := value in value.")
  assert(!out.contains("val value = value"),out)
 }
 test("tuple-let bindings do not capture their own initializer") {
  val out=generate("Definition identity (value : nat) : nat := let (value, ignored) := (value, value) in value.")
  assert(!out.contains("val (value, ignored) = (value, value)"),out)
 }
}
