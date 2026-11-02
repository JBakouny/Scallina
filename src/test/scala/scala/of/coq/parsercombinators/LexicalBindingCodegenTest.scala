package scala.of.coq.parsercombinators

import org.scalatest.FunSuite
import scala.of.coq.parsercombinators.compiler.{ScalaOfCoq, Currify}
import scala.of.coq.parsercombinators.parser._

class LexicalBindingCodegenTest extends FunSuite {
  private val context = CoqParser("""Record box := Box { payload : nat }.
    Record generic_box (A : Type) := GenericBox { content : A }.
    Inductive pair_value := PairValue (left right : nat).""").get
  private def generate(source: String): String = {
    val parsed = CoqParser(source)
    assert(parsed.successful, parsed.toString)
    new ScalaOfCoq(parsed.get, Currify, exactNumerics = true, nativeFullConstructors = true,
      recordContext = context.collect { case r: Record => r },
      inductiveContext = context.collect { case i: Inductive => i }).generateScalaCode
  }
  test("successor remains one operand under multiplication and nested addition") {
    val output = generate("""From Stdlib Require Import NArith. Open Scope N_scope.
      Definition scale (value : N) : N := N.succ value * 2.
      Definition right_scale (value : N) : N := 2 * N.succ value.
      Definition nested (value : N) : N := N.succ (N.succ value) * 2.""")
    assert(output.contains("(value + BigInt(\"1\")) * BigInt(\"2\")"))
    assert(output.contains("BigInt(\"2\") * (value + BigInt(\"1\"))"))
  }
  test("function binders shadow imported record projections") {
    val output = generate("Definition read (payload : nat -> nat) (value : nat) : nat := payload value.")
    assert(output.contains("payload(value)")); assert(!output.contains("value.payload"))
  }
  test("let bindings shadow imported record projections only in their body") {
    val output = generate("Definition read (value : nat) : nat := let payload := fun x : nat => x in payload value.")
    assert(output.contains("payload(value)")); assert(!output.contains("value.payload"))
  }
  test("lambda binders shadow imported record projections") {
    val output = generate("Definition read (value : nat) := fun payload : nat -> nat => payload value.")
    assert(output.contains("payload(value)")); assert(!output.contains("value.payload"))
  }
  test("function binders shadow imported inductive constructors") {
    val output = generate("Definition combine (PairValue : nat -> nat -> nat) (left right : nat) := PairValue left right.")
    assert(output.contains("PairValue(left)(right)")); assert(!output.contains("new PairValue"))
  }
  test("let bindings shadow imported inductive constructors") {
    val output = generate("Definition combine (left right : nat) := let PairValue := fun x y : nat => x in PairValue left right.")
    assert(output.contains("PairValue(left)(right)")); assert(!output.contains("new PairValue"))
  }
  test("record constructor type-argument metadata cannot override a function binder") {
    val output = generate("Definition combine (GenericBox : nat -> nat -> nat) (left right : nat) := GenericBox left right.")
    assert(output.contains("GenericBox(left)(right)")); assert(!output.contains("GenericBox["))
  }
  test("match pattern bindings shadow projections within the matching branch") {
    val output = generate("""Definition choose (function : nat -> nat) (value : nat) :=
      match Some function with | Some payload => payload value | None => value end.""")
    assert(output.contains("payload(value)")); assert(!output.contains("value.payload"))
  }
  test("fixpoint parameters shadow projections through recursive match bodies") {
    val output = generate("""From Stdlib Require Import List. Import ListNotations.
      Fixpoint apply_values (payload : nat -> nat) (values : list nat) : list nat :=
      match values with | nil => nil | value :: rest => payload value :: apply_values payload rest end.""")
    assert(output.contains("payload(value)")); assert(!output.contains("value.payload"))
  }
  test("lexical scope ends before subsequent definitions use imported metadata") {
    val output = generate("""Definition shadow (payload : nat -> nat) (value : nat) := payload value.
      Definition project (value : box) := payload value.
      Definition construct (left right : nat) := PairValue left right.""")
    assert(output.contains("payload(value)")); assert(output.contains("value.payload")); assert(output.contains("new PairValue(left, right)"))
  }

  test("tuple-let bindings shadow imported projections") {
    val output = generate("Definition read (function : nat -> nat) (value : nat) := let (payload, ignored) := (function, function) in payload value.")
    assert(output.contains("payload(value)")); assert(!output.contains("value.payload"))
  }
  test("pattern bindings do not leak into sibling branches") {
    val output = generate("""Definition choose (functions : option (nat -> nat)) (number : nat) (boxed : box) :=
      match functions with | Some payload => payload number | None => payload boxed end.""")
    assert(output.contains("payload(number)")); assert(output.contains("boxed.payload"))
  }
  test("unqualified standard library names respect local binders") {
    val output = generate("""From Stdlib Require Import List.
      Definition custom_map (map : nat -> nat -> nat) (left right : nat) := map left right.
      Definition custom_length (length : nat -> nat) (value : nat) := length value.""")
    assert(output.contains("map(left)(right)")); assert(output.contains("length(value)")); assert(!output.contains(".length"))
  }
}
