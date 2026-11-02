package scala.of.coq.parsercombinators

import org.scalatest.FunSuite
import scala.of.coq.parsercombinators.parser._
import scala.of.coq.parsercombinators.compiler.{ScalaOfCoq, Currify}

class LogicalTermParserTest extends FunSuite {
  private def q(s: String): Qualid = Qualid(List(Ident(s)))
  private def parsed(s: String): Term = {
    val result = CoqTermParser(s)
    assert(result.successful, result.toString)
    result.get.asInstanceOf[Term]
  }

  test("forall trailing typed names share one binder type") {
    assert(parsed("forall left right : nat, left = right") ==
      ForAll(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("left"))), Name(Some(Ident("right")))), q("nat")))),
        InfixOperator(q("left"), "=", q("right"))))
  }

  test("typed forall preserves preceding grouped and implicit binders") {
    assert(parsed("forall {A : Type} (seed : A) left right : A, left = right") ==
      ForAll(Binders(List(ImplicitBinder(List(Name(Some(Ident("A")))), Some(Type)),
        ExplicitBinderWithType(List(Name(Some(Ident("seed")))), q("A")),
        ExplicitBinderWithType(List(Name(Some(Ident("left"))), Name(Some(Ident("right")))), q("A")))),
        InfixOperator(q("left"), "=", q("right"))))
  }

  test("disjunction binds less tightly than equality and conjunction") {
    val code = """a = 1 \/ b = 2 /\ c = 3"""
    val eq1 = InfixOperator(q("a"), "=", Number(1))
    val eq2 = InfixOperator(q("b"), "=", Number(2))
    val eq3 = InfixOperator(q("c"), "=", Number(3))
    assert(parsed(code) == InfixOperator(eq1, """\/""", InfixOperator(eq2, """/\""", eq3)))
  }

  test("logical parentheses remain explicit and disjunction associates right") {
    assert(parsed("""(P \/ Q) /\ R""") == InfixOperator(
      BetweenParenthesis(InfixOperator(q("P"), """\/""", q("Q"))), """/\""", q("R")))
    assert(parsed("""P \/ Q \/ R""") == InfixOperator(q("P"), """\/""", InfixOperator(q("Q"), """\/""", q("R"))))
  }

  test("typed lambda uses the same trailing binder rule") {
    assert(parsed("fun left right : nat => left") ==
      Fun(Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("left"))), Name(Some(Ident("right")))), q("nat")))), q("left")))
  }

  test("logical formulas are parsed in assertions and never emitted as runtime operators") {
    val source = """Lemma either_reflexive : forall x : nat, x = x \/ x <> x.
      Proof. intros. left. reflexivity. Qed.
      Definition zero : nat := 0."""
    val trees = CoqParser(source)
    assert(trees.successful, trees.toString)
    val code = new ScalaOfCoq(trees.get, Currify, exactNumerics = true).generateScalaCode
    assert(!code.contains("either_reflexive"))
    val unsupported = CoqParser("""Definition formula := P \/ Q.""")
    assert(unsupported.successful, unsupported.toString)
    val error = intercept[IllegalStateException] {
      new ScalaOfCoq(unsupported.get, Currify, exactNumerics = true).generateScalaCode
    }
    assert(error.getMessage.contains("requires proof erasure"))
  }

  test("explicit Prop families and assumption queries do not become runtime declarations") {
    val source = """Inductive evidence : nat -> Prop :=
      | Evidence : forall n : nat, evidence n.
      Definition predicate (n : nat) : Prop := n = n.
      Print Assumptions predicate.
      Definition value : nat := 1."""
    val trees = CoqParser(source)
    assert(trees.successful, trees.toString)
    val code = new ScalaOfCoq(trees.get, Currify, exactNumerics = true).generateScalaCode
    assert(!code.contains("evidence"))
    assert(!code.contains("Evidence"))
    assert(!code.contains("predicate"))
    assert(code.contains("value"))
  }

  test("mutual Prop families are retained as one syntax node and erased together") {
    val source = """Inductive even : nat -> Prop :=
      | EvenZero : even 0
      | EvenSucc : forall n : nat, odd n -> even (S n)
      with odd : nat -> Prop :=
      | OddSucc : forall n : nat, even n -> odd (S n)."""
    val trees = CoqParser(source)
    assert(trees.successful, trees.toString)
    assert(trees.get.size == 1)
    assert(new ScalaOfCoq(trees.get, Currify, exactNumerics = true).generateScalaCode.isEmpty)
  }

  test("computational mutual inductives remain unsupported instead of being erased") {
    val trees = CoqParser("Inductive tree : Type := | Node : forest -> tree with forest : Type := | Empty : forest.")
    assert(trees.successful, trees.toString)
    intercept[IllegalStateException] {
      new ScalaOfCoq(trees.get, Currify, exactNumerics = true).generateScalaCode
    }
  }

  test("sumbool notation is parsed without claiming a runtime proof-erasure mapping") {
    val trees = CoqParser("""Definition decide : forall left right : nat, {left = right} + {left <> right} := nat_eq_dec.""")
    assert(trees.successful, trees.toString)
    intercept[IllegalStateException] {
      new ScalaOfCoq(trees.get, Currify, exactNumerics = true).generateScalaCode
    }
  }

  test("an imported record context lowers projections without emitting its declaration") {
    val records = CoqParser("Record box := Box { payload : nat }.").get.collect { case r: Record => r }
    val trees = CoqParser("Definition read (value : box) := payload value.").get
    val code = new ScalaOfCoq(trees, Currify, exactNumerics = true, recordContext = records).generateScalaCode
    assert(code.contains("value.payload"))
    assert(!code.contains("trait box"))
  }

  test("ambiguous imported record projections fail closed") {
    val records = CoqParser("Record box := Box { payload : nat }. Record other := Other { payload : nat }.").get.collect { case r: Record => r }
    val trees = CoqParser("Definition read (value : box) := payload value.").get
    val error = intercept[IllegalArgumentException] {
      new ScalaOfCoq(trees, Currify, exactNumerics = true, recordContext = records).generateScalaCode
    }
    assert(error.getMessage.contains("Ambiguous"))
  }

  test("ambiguous imported record constructors fail closed") {
    val records = CoqParser("Record box := Build { payload : nat }. Record other := Build { count : nat }.").get.collect { case r: Record => r }
    intercept[IllegalArgumentException] {
      new ScalaOfCoq(Nil, Currify, exactNumerics = true, recordContext = records).generateScalaCode
    }
  }

  test("local definitions shadow imported projection metadata") {
    val records = CoqParser("Record box := Box { payload : nat }.").get.collect { case r: Record => r }
    val trees = CoqParser("Definition payload (value : nat) := value. Definition read (value : nat) := payload value.").get
    val code = new ScalaOfCoq(trees, Currify, exactNumerics = true, recordContext = records).generateScalaCode
    assert(code.contains("payload(value)"))
    assert(!code.contains("value.payload"))
  }

  test("negation scopes over an application inside an implication") {
    val result = parsed("P -> ~ predicate x")
    assert(result.toCoqCode.contains("~"))
    assert(result.toCoqCode.contains("predicate x"))
    val trees = CoqParser("Lemma statement : P -> ~ predicate x. Proof. admit. Admitted.")
    assert(trees.successful, trees.toString)
    assert(new ScalaOfCoq(trees.get, Currify).generateScalaCode.isEmpty)
    assert(parsed("""~ P /\ Q""") == InfixOperator(LogicalNot(q("P")), """/\""", q("Q")))
    assert(parsed("~ P -> Q") == Term_->(LogicalNot(q("P")), q("Q")))
  }

  test("existential typed binders and conjunction parse inside an implication") {
    val trees = CoqParser("""Lemma witness : P -> exists left right : nat, left = right /\ Q.
      Proof. admit. Admitted.""")
    assert(trees.successful, trees.toString)
    assert(new ScalaOfCoq(trees.get, Currify).generateScalaCode.isEmpty)
  }
}
