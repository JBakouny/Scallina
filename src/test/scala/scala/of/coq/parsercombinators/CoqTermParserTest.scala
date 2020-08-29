package scala.of.coq.parsercombinators

import org.scalatest.FunSuite
import org.scalatest.Matchers.convertToAnyShouldWrapper

import scala.of.coq.parsercombinators.CustomMatchers.parse
import scala.of.coq.parsercombinators.parser.{
  ApplicationProjection,
  Argument,
  BetweenParenthesis,
  Binders,
  ConstructorPattern,
  CoqTermParser,
  CurriedTermApplication,
  DepRetType,
  ExplicitApplicationProjection,
  ExplicitBinderWithType,
  ExplicitQualidApplication,
  ExplicitSimpleBinder,
  FixAnnotation,
  FixBody,
  ForAll,
  Fun,
  Ident,
  ImplicitBinder,
  InfixOperator,
  LetConstructorArgsIn,
  LetFixIn,
  LetPatternIn,
  Match,
  MatchItem,
  MatchItemPattern,
  MultPattern,
  Name,
  Number,
  PatternEquation,
  Prop,
  Qualid,
  QualidPattern,
  ReturnType,
  Set,
  SimpleLetIn,
  SimpleProjection,
  TermIf,
  Term_%,
  Term_->,
  Term_:,
  Term_:>,
  Term_<:,
  TupleValue,
  Type,
  UncurriedTermApplication,
  UnderscorePattern
}

class CoqTermParserTest extends FunSuite {

  test("""Testing "forall a, (a -> a)" """) {
    CoqTermParser("forall a, (a -> a)") should parse(
      ForAll(
        Binders(List(ExplicitSimpleBinder(Name(Some(Ident("a")))))),
        BetweenParenthesis(Term_->(Qualid(List(Ident("a"))), Qualid(List(Ident("a")))))
      )
    )
  }

  test("""Testing the support of (* Coq comments *) """) {
    CoqTermParser("""
      (* Coq comments are supported by this lexer *)

      (* They can be inserted before a term *)

      forall a, (a -> (* In the middle of a term *) a)

      (* or at the end of a term *)
      """) should parse(
      ForAll(
        Binders(List(ExplicitSimpleBinder(Name(Some(Ident("a")))))),
        BetweenParenthesis(Term_->(Qualid(List(Ident("a"))), Qualid(List(Ident("a")))))
      )
    )
  }

  test("""Testing "forall a b c, (a -> b) -> (b -> c) -> (a -> c)" """) {
    CoqTermParser("forall a b c, (a -> b) -> (b -> c) -> (a -> c)") should parse(
      ForAll(
        Binders(
          List(
            ExplicitSimpleBinder(Name(Some(Ident("a")))),
            ExplicitSimpleBinder(Name(Some(Ident("b")))),
            ExplicitSimpleBinder(Name(Some(Ident("c"))))
          )
        ),
        Term_->(
          BetweenParenthesis(Term_->(Qualid(List(Ident("a"))), Qualid(List(Ident("b"))))),
          Term_->(
            BetweenParenthesis(Term_->(Qualid(List(Ident("b"))), Qualid(List(Ident("c"))))),
            BetweenParenthesis(Term_->(Qualid(List(Ident("a"))), Qualid(List(Ident("c")))))
          )
        )
      )
    )
  }

  test("""Testing "fun s => 5" """) {
    CoqTermParser("fun s => 5") should parse(
      Fun(Binders(List(ExplicitSimpleBinder(Name(Some(Ident("s")))))), Number(5))
    )
  }

  test("""Testing "fun (x : nat) => x" """) {
    CoqTermParser("fun (x : nat) => x") should parse(
      Fun(
        Binders(List(ExplicitBinderWithType(List(Name(Some(Ident("x")))), Qualid(List(Ident("nat")))))),
        Qualid(List(Ident("x")))
      )
    )
  }

  test("""Testing "fun {A} (l r: A) => l" """) {
    CoqTermParser("fun {A} (l r: A) => l") should parse(
      Fun(
        Binders(
          List(
            ImplicitBinder(List(Name(Some(Ident("A")))), None),
            ExplicitBinderWithType(List(Name(Some(Ident("l"))), Name(Some(Ident("r")))), Qualid(List(Ident("A"))))
          )
        ),
        Qualid(List(Ident("l")))
      )
    )
  }

  test("""Testing "fun {A B} (l: A) (r: B) => r" """) {
    CoqTermParser("fun {A B} (l: A) (r: B) => r") should parse(
      Fun(
        Binders(
          List(
            ImplicitBinder(List(Name(Some(Ident("A"))), Name(Some(Ident("B")))), None),
            ExplicitBinderWithType(List(Name(Some(Ident("l")))), Qualid(List(Ident("A")))),
            ExplicitBinderWithType(List(Name(Some(Ident("r")))), Qualid(List(Ident("B"))))
          )
        ),
        Qualid(List(Ident("r")))
      )
    )
  }

  test("""Testing "fun {A : Type} (l r : A) => l" """) {
    CoqTermParser("fun {A : Type} (l r : A) => l") should parse(
      Fun(
        Binders(
          List(
            ImplicitBinder(List(Name(Some(Ident("A")))), Some(Type)),
            ExplicitBinderWithType(List(Name(Some(Ident("l"))), Name(Some(Ident("r")))), Qualid(List(Ident("A"))))
          )
        ),
        Qualid(List(Ident("l")))
      )
    )
  }

  test("""Testing "fun {A B : Type} (l : A) (r : B) => l" """) {
    CoqTermParser("fun {A B : Type} (l : A) (r : B) => l") should parse(
      Fun(
        Binders(
          List(
            ImplicitBinder(List(Name(Some(Ident("A"))), Name(Some(Ident("B")))), Some(Type)),
            ExplicitBinderWithType(List(Name(Some(Ident("l")))), Qualid(List(Ident("A")))),
            ExplicitBinderWithType(List(Name(Some(Ident("r")))), Qualid(List(Ident("B"))))
          )
        ),
        Qualid(List(Ident("l")))
      )
    )
  }

  test("""Testing "fun (a b c : nat) => b" """) {
    CoqTermParser("fun (a b c : nat) => b") should parse(
      Fun(
        Binders(
          List(
            ExplicitBinderWithType(
              List(Name(Some(Ident("a"))), Name(Some(Ident("b"))), Name(Some(Ident("c")))),
              Qualid(List(Ident("nat")))
            )
          )
        ),
        Qualid(List(Ident("b")))
      )
    )
  }

  test("""Testing "fun (A : Type) (a b c : A) => b" """) {
    CoqTermParser("fun (A : Type) (a b c : A) => b") should parse(
      Fun(
        Binders(
          List(
            ExplicitBinderWithType(List(Name(Some(Ident("A")))), Type),
            ExplicitBinderWithType(
              List(Name(Some(Ident("a"))), Name(Some(Ident("b"))), Name(Some(Ident("c")))),
              Qualid(List(Ident("A")))
            )
          )
        ),
        Qualid(List(Ident("b")))
      )
    )
  }

  test("""Testing "fun (_ b _ : nat) => b" """) {
    CoqTermParser("fun (_ b _ : nat) => b") should parse(
      Fun(
        Binders(
          List(ExplicitBinderWithType(List(Name(None), Name(Some(Ident("b"))), Name(None)), Qualid(List(Ident("nat")))))
        ),
        Qualid(List(Ident("b")))
      )
    )
  }

  test("""Testing "fun s _ => 5" """) {
    CoqTermParser("fun s _ => 5") should parse(
      Fun(Binders(List(ExplicitSimpleBinder(Name(Some(Ident("s")))), ExplicitSimpleBinder(Name(None)))), Number(5))
    )
  }

  test("""Testing "fun s _ a => 5" """) {
    CoqTermParser("fun s _ a => 5") should parse(
      Fun(
        Binders(
          List(
            ExplicitSimpleBinder(Name(Some(Ident("s")))),
            ExplicitSimpleBinder(Name(None)),
            ExplicitSimpleBinder(Name(Some(Ident("a"))))
          )
        ),
        Number(5)
      )
    )
  }

  test("""Testing
            let fix rightMost {A : Type} (t : BinTree) : A := match t with
             L x => x
            | N l r => rightMost r
            end in rightMost (N (L 3) (N (L 5) (L 7)))
          """) {
    CoqTermParser("""
                let fix rightMost {A : Type} (t : BinTree) : A := match t with
                 L x => x
                | N l r => rightMost r
                end in rightMost (N (L 3) (N (L 5) (L 7)))
                """) should parse(
      LetFixIn(
        FixBody(
          Ident("rightMost"),
          Binders(
            List(
              ImplicitBinder(List(Name(Some(Ident("A")))), Some(Type)),
              ExplicitBinderWithType(List(Name(Some(Ident("t")))), Qualid(List(Ident("BinTree"))))
            )
          ),
          None,
          Some(Qualid(List(Ident("A")))),
          Match(
            List(MatchItem(Qualid(List(Ident("t"))), None, None)),
            None,
            List(
              PatternEquation(
                List(
                  MultPattern(
                    List(ConstructorPattern(Qualid(List(Ident("L"))), List(QualidPattern(Qualid(List(Ident("x")))))))
                  )
                ),
                Qualid(List(Ident("x")))
              ),
              PatternEquation(
                List(
                  MultPattern(
                    List(
                      ConstructorPattern(
                        Qualid(List(Ident("N"))),
                        List(QualidPattern(Qualid(List(Ident("l")))), QualidPattern(Qualid(List(Ident("r")))))
                      )
                    )
                  )
                ),
                UncurriedTermApplication(
                  Qualid(List(Ident("rightMost"))),
                  List(Argument(None, Qualid(List(Ident("r")))))
                )
              )
            )
          )
        ),
        UncurriedTermApplication(
          Qualid(List(Ident("rightMost"))),
          List(
            Argument(
              None,
              BetweenParenthesis(
                UncurriedTermApplication(
                  Qualid(List(Ident("N"))),
                  List(
                    Argument(
                      None,
                      BetweenParenthesis(
                        UncurriedTermApplication(Qualid(List(Ident("L"))), List(Argument(None, Number(3))))
                      )
                    ),
                    Argument(
                      None,
                      BetweenParenthesis(
                        UncurriedTermApplication(
                          Qualid(List(Ident("N"))),
                          List(
                            Argument(
                              None,
                              BetweenParenthesis(
                                UncurriedTermApplication(Qualid(List(Ident("L"))), List(Argument(None, Number(5))))
                              )
                            ),
                            Argument(
                              None,
                              BetweenParenthesis(
                                UncurriedTermApplication(Qualid(List(Ident("L"))), List(Argument(None, Number(7))))
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  }

  test("""Testing "let x := 3 in x" """) {
    CoqTermParser("let x := 3 in x") should parse(
      SimpleLetIn(Ident("x"), None, None, Number(3), Qualid(List(Ident("x"))))
    )
  }

  test("""Testing "let x := 3 in fun y => y % x" """) {
    CoqTermParser("let x := 3 in fun y => y % x") should parse(
      SimpleLetIn(
        Ident("x"),
        None,
        None,
        Number(3),
        Fun(Binders(List(ExplicitSimpleBinder(Name(Some(Ident("y")))))), Term_%(Qualid(List(Ident("y"))), Ident("x")))
      )
    )
  }

  test("""Testing "let sumAlias (a b : nat) := sum a b in sumAlias 3 7" """) {
    CoqTermParser("let sumAlias (a b : nat) := sum a b in sumAlias 3 7") should parse(
      SimpleLetIn(
        Ident("sumAlias"),
        Some(
          Binders(
            List(
              ExplicitBinderWithType(List(Name(Some(Ident("a"))), Name(Some(Ident("b")))), Qualid(List(Ident("nat"))))
            )
          )
        ),
        None,
        UncurriedTermApplication(
          Qualid(List(Ident("sum"))),
          List(Argument(None, Qualid(List(Ident("a")))), Argument(None, Qualid(List(Ident("b")))))
        ),
        UncurriedTermApplication(
          Qualid(List(Ident("sumAlias"))),
          List(Argument(None, Number(3)), Argument(None, Number(7)))
        )
      )
    )
  }

  test("""Testing "let fix right (l r : nat) : nat := r in right 7 3" """) {
    CoqTermParser("let fix right (l r : nat) : nat := r in right 7 3") should parse(
      LetFixIn(
        FixBody(
          Ident("right"),
          Binders(
            List(
              ExplicitBinderWithType(List(Name(Some(Ident("l"))), Name(Some(Ident("r")))), Qualid(List(Ident("nat"))))
            )
          ),
          None,
          Some(Qualid(List(Ident("nat")))),
          Qualid(List(Ident("r")))
        ),
        UncurriedTermApplication(
          Qualid(List(Ident("right"))),
          List(Argument(None, Number(7)), Argument(None, Number(3)))
        )
      )
    )
  }

  test("""Testing "let fix right (l r : nat) { struct l } := r in right 7 3" """) {
    CoqTermParser("let fix right (l r : nat) { struct l } := r in right 7 3") should parse(
      LetFixIn(
        FixBody(
          Ident("right"),
          Binders(
            List(
              ExplicitBinderWithType(List(Name(Some(Ident("l"))), Name(Some(Ident("r")))), Qualid(List(Ident("nat"))))
            )
          ),
          Some(FixAnnotation(Ident("l"))),
          None,
          Qualid(List(Ident("r")))
        ),
        UncurriedTermApplication(
          Qualid(List(Ident("right"))),
          List(Argument(None, Number(7)), Argument(None, Number(3)))
        )
      )
    )
  }

  test("""Testing "let (l, r) := Node 3 7 in sum l r" """) {
    CoqTermParser("let (l, r) := Node 3 7 in sum l r") should parse(
      LetConstructorArgsIn(
        List(Name(Some(Ident("l"))), Name(Some(Ident("r")))),
        None,
        UncurriedTermApplication(
          Qualid(List(Ident("Node"))),
          List(Argument(None, Number(3)), Argument(None, Number(7)))
        ),
        UncurriedTermApplication(
          Qualid(List(Ident("sum"))),
          List(Argument(None, Qualid(List(Ident("l")))), Argument(None, Qualid(List(Ident("r")))))
        )
      )
    )
  }

  test("""Testing "let (l, r) as p return nat := Node 3 7 in sum l r" """) {
    CoqTermParser("let (l, r) as p return nat := Node 3 7 in sum l r") should parse(
      LetConstructorArgsIn(
        List(Name(Some(Ident("l"))), Name(Some(Ident("r")))),
        Some(DepRetType(Some(Name(Some(Ident("p")))), ReturnType(Qualid(List(Ident("nat")))))),
        UncurriedTermApplication(
          Qualid(List(Ident("Node"))),
          List(Argument(None, Number(3)), Argument(None, Number(7)))
        ),
        UncurriedTermApplication(
          Qualid(List(Ident("sum"))),
          List(Argument(None, Qualid(List(Ident("l")))), Argument(None, Qualid(List(Ident("r")))))
        )
      )
    )
  }

  test("""Testing "let ' pair l r := pair 3 7 return nat in sum l r" """) {
    CoqTermParser("let ' pair l r := pair 3 7 return nat in sum l r") should parse(
      LetPatternIn(
        ConstructorPattern(
          Qualid(List(Ident("pair"))),
          List(QualidPattern(Qualid(List(Ident("l")))), QualidPattern(Qualid(List(Ident("r")))))
        ),
        UncurriedTermApplication(
          Qualid(List(Ident("pair"))),
          List(Argument(None, Number(3)), Argument(None, Number(7)))
        ),
        Some(ReturnType(Qualid(List(Ident("nat"))))),
        UncurriedTermApplication(
          Qualid(List(Ident("sum"))),
          List(Argument(None, Qualid(List(Ident("l")))), Argument(None, Qualid(List(Ident("r")))))
        )
      )
    )
  }

  test("""Testing "let ' pair l _ := pair 3 7 return nat in l" """) {
    CoqTermParser("let ' pair l _ := pair 3 7 return nat in l") should parse(
      LetPatternIn(
        ConstructorPattern(
          Qualid(List(Ident("pair"))),
          List(QualidPattern(Qualid(List(Ident("l")))), UnderscorePattern)
        ),
        UncurriedTermApplication(
          Qualid(List(Ident("pair"))),
          List(Argument(None, Number(3)), Argument(None, Number(7)))
        ),
        Some(ReturnType(Qualid(List(Ident("nat"))))),
        Qualid(List(Ident("l")))
      )
    )
  }

  test("""Testing "if a then 5 else 7" """) {
    CoqTermParser("if a then 5 else 7") should parse(TermIf(Qualid(List(Ident("a"))), None, Number(5), Number(7)))
  }

  test("""Testing "if a as b return nat then 5 else 7" """) {
    CoqTermParser("if a as b return nat then 5 else 7") should parse(
      TermIf(
        Qualid(List(Ident("a"))),
        Some(DepRetType(Some(Name(Some(Ident("b")))), ReturnType(Qualid(List(Ident("nat")))))),
        Number(5),
        Number(7)
      )
    )
  }

  test("""Testing "if a return nat then 5 else 7" """) {
    CoqTermParser("if a return nat then 5 else 7") should parse(
      TermIf(
        Qualid(List(Ident("a"))),
        Some(DepRetType(None, ReturnType(Qualid(List(Ident("nat")))))),
        Number(5),
        Number(7)
      )
    )
  }

  test("""Testing "2 : a" """) {
    CoqTermParser("2 : a") should parse(Term_:(Number(2), Qualid(List(Ident("a")))))
  }

  test("""Testing "2 <: a" """) {
    CoqTermParser("2 <: a") should parse(Term_<:(Number(2), Qualid(List(Ident("a")))))
  }

  test("""Testing "a :>" """) {
    CoqTermParser("a :>") should parse(Term_:>(Qualid(List(Ident("a")))))
  }

  test("""Testing "a -> a" """) {
    CoqTermParser("a -> a") should parse(Term_->(Qualid(List(Ident("a"))), Qualid(List(Ident("a")))))
  }

  test("""Testing "sum (x := 7) 3" """) {
    CoqTermParser("sum (x := 7) 3") should parse(
      UncurriedTermApplication(
        Qualid(List(Ident("sum"))),
        List(Argument(Some(Ident("x")), Number(7)), Argument(None, Number(3)))
      )
    )
  }

  test("""Testing "sum (x := 7) (x := 3)" """) {
    CoqTermParser("sum (x := 7) (x := 3)") should parse(
      UncurriedTermApplication(
        Qualid(List(Ident("sum"))),
        List(Argument(Some(Ident("x")), Number(7)), Argument(Some(Ident("x")), Number(3)))
      )
    )
  }

  test("""Testing "sum 7 3" """) {
    CoqTermParser("sum 7 3") should parse(
      UncurriedTermApplication(Qualid(List(Ident("sum"))), List(Argument(None, Number(7)), Argument(None, Number(3))))
    )
  }

  test("""Testing a basic version of the currify method""") {
    // Important note: this method does not yet support recursive UncurriedTermApplications or general ASTs
    // format: OFF
    assert(
      UncurriedTermApplication(
        Qualid(List(Ident("sum"))),
        List(
          Argument(None, Number(7)),
          Argument(None, Number(3))))
                .currify
                  ===
      CurriedTermApplication(
        CurriedTermApplication(
          Qualid(List(Ident("sum"))),
          Argument(None, Number(7))),
        Argument(None, Number(3)))
    )
    // format: ON
  }

  test("""Testing "sum 7 (x := 3)" """) {
    CoqTermParser("sum 7 (x := 3)") should parse(
      UncurriedTermApplication(
        Qualid(List(Ident("sum"))),
        List(Argument(None, Number(7)), Argument(Some(Ident("x")), Number(3)))
      )
    )
  }

  test("""Testing "sum (S 0) (S (S 0))" """) {
    CoqTermParser("sum (S 0) (S (S 0))") should parse(
      UncurriedTermApplication(
        Qualid(List(Ident("sum"))),
        List(
          Argument(
            None,
            BetweenParenthesis(UncurriedTermApplication(Qualid(List(Ident("S"))), List(Argument(None, Number(0)))))
          ),
          Argument(
            None,
            BetweenParenthesis(
              UncurriedTermApplication(
                Qualid(List(Ident("S"))),
                List(
                  Argument(
                    None,
                    BetweenParenthesis(
                      UncurriedTermApplication(Qualid(List(Ident("S"))), List(Argument(None, Number(0))))
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  }

  test("""Testing "sum 0 (S 0)" """) {
    CoqTermParser("sum 0 (S 0)") should parse(
      UncurriedTermApplication(
        Qualid(List(Ident("sum"))),
        List(
          Argument(None, Number(0)),
          Argument(
            None,
            BetweenParenthesis(UncurriedTermApplication(Qualid(List(Ident("S"))), List(Argument(None, Number(0)))))
          )
        )
      )
    )
  }

  test("""Testing "@Tree A" """) {
    CoqTermParser("@Tree A") should parse(
      ExplicitQualidApplication(Qualid(List(Ident("Tree"))), List(Qualid(List(Ident("A")))))
    )
  }

  test("""Testing "@ Tree A B" """) {
    CoqTermParser("@ Tree A B") should parse(
      ExplicitQualidApplication(Qualid(List(Ident("Tree"))), List(Qualid(List(Ident("A"))), Qualid(List(Ident("B")))))
    )
  }

  test("""Testing "2 % z" """) {
    CoqTermParser("2 % z") should parse(Term_%(Number(2), Ident("z")))
  }

  test("""Testing "3 + 7" """) {
    CoqTermParser("3 + 7") should parse(InfixOperator(Number(3), "+", Number(7)))
  }

  test("""Testing "7 - 3 - 2" """) {
    CoqTermParser("7 - 3 - 2") should parse(InfixOperator(Number(7), "-", InfixOperator(Number(3), "-", Number(2))))
  }

  test("""Testing "3 * 7 * 3" """) {
    CoqTermParser("3 * 7 * 3") should parse(InfixOperator(Number(3), "*", InfixOperator(Number(7), "*", Number(3))))
  }

  test("""Testing "3 / 7" """) {
    CoqTermParser("3 / 7") should parse(InfixOperator(Number(3), "/", Number(7)))
  }

  test("""Testing "3 > 7" """) {
    CoqTermParser("3 > 7") should parse(InfixOperator(Number(3), ">", Number(7)))
  }

  test("""Testing "3 < 7" """) {
    CoqTermParser("3 > 7") should parse(InfixOperator(Number(3), ">", Number(7)))
  }

  test("""Testing "3 = 7" """) {
    CoqTermParser("3 = 7") should parse(InfixOperator(Number(3), "=", Number(7)))
  }

  test("""Testing "3 <=? 7" """) {
    CoqTermParser("3 <=? 7") should parse(InfixOperator(Number(3), "<=?", Number(7)))
  }

  test("""Testing "3 <= 7" """) {
    CoqTermParser("3 <= 7") should parse(InfixOperator(Number(3), "<=", Number(7)))
  }

  test("""Testing "3 >= 7" """) {
    CoqTermParser("3 >= 7") should parse(InfixOperator(Number(3), ">=", Number(7)))
  }

  test("""Testing "3 <? 7" """) {
    CoqTermParser("3 <? 7") should parse(InfixOperator(Number(3), "<?", Number(7)))
  }

  test("""Testing "3 =? 7" """) {
    CoqTermParser("3 =? 7") should parse(InfixOperator(Number(3), "=?", Number(7)))
  }

  test("""Testing "x :: xs" """) {
    CoqTermParser("x :: xs") should parse(InfixOperator(Qualid(List(Ident("x"))), "::", Qualid(List(Ident("xs")))))
  }

  test(""" Testing
    match Node (Node Leaf Leaf) (Node Leaf Leaf) with
      Leaf  => Leaf
    | Node l r => l
    end
    """) {

    CoqTermParser("""
    match Node (Node Leaf Leaf) (Node Leaf Leaf) with
      Leaf => Leaf
    | Node l r => l
    end
    """) should parse(
      Match(
        List(
          MatchItem(
            UncurriedTermApplication(
              Qualid(List(Ident("Node"))),
              List(
                Argument(
                  None,
                  BetweenParenthesis(
                    UncurriedTermApplication(
                      Qualid(List(Ident("Node"))),
                      List(Argument(None, Qualid(List(Ident("Leaf")))), Argument(None, Qualid(List(Ident("Leaf")))))
                    )
                  )
                ),
                Argument(
                  None,
                  BetweenParenthesis(
                    UncurriedTermApplication(
                      Qualid(List(Ident("Node"))),
                      List(Argument(None, Qualid(List(Ident("Leaf")))), Argument(None, Qualid(List(Ident("Leaf")))))
                    )
                  )
                )
              )
            ),
            None,
            None
          )
        ),
        None,
        List(
          PatternEquation(
            List(MultPattern(List(QualidPattern(Qualid(List(Ident("Leaf"))))))),
            Qualid(List(Ident("Leaf")))
          ),
          PatternEquation(
            List(
              MultPattern(
                List(
                  ConstructorPattern(
                    Qualid(List(Ident("Node"))),
                    List(QualidPattern(Qualid(List(Ident("l")))), QualidPattern(Qualid(List(Ident("r")))))
                  )
                )
              )
            ),
            Qualid(List(Ident("l")))
          )
        )
      )
    )

  }

  test(""" Testing
    match H in eq _ _ z return eq A z x with
    | eq_refl _ _ => eq_refl A x
    end
    """) {

    CoqTermParser("""
    match H in eq _ _ z return eq A z x with
    | eq_refl _ _ => eq_refl A x
    end
    """) should parse(
      Match(
        List(
          MatchItem(
            Qualid(List(Ident("H"))),
            None,
            Some(
              MatchItemPattern(
                Qualid(List(Ident("eq"))),
                List(UnderscorePattern, UnderscorePattern, QualidPattern(Qualid(List(Ident("z")))))
              )
            )
          )
        ),
        Some(
          ReturnType(
            UncurriedTermApplication(
              Qualid(List(Ident("eq"))),
              List(
                Argument(None, Qualid(List(Ident("A")))),
                Argument(None, Qualid(List(Ident("z")))),
                Argument(None, Qualid(List(Ident("x"))))
              )
            )
          )
        ),
        List(
          PatternEquation(
            List(
              MultPattern(
                List(ConstructorPattern(Qualid(List(Ident("eq_refl"))), List(UnderscorePattern, UnderscorePattern)))
              )
            ),
            UncurriedTermApplication(
              Qualid(List(Ident("eq_refl"))),
              List(Argument(None, Qualid(List(Ident("A")))), Argument(None, Qualid(List(Ident("x")))))
            )
          )
        )
      )
    )
  }

  test("""Testing "record.(field)" """) {
    CoqTermParser("record.(field)") should parse(
      SimpleProjection(Qualid(List(Ident("record"))), Qualid(List(Ident("field"))))
    )
  }

  test("""Testing "record.(field 3 7)" """) {
    CoqTermParser("record.(field 3 7)") should parse(
      ApplicationProjection(
        Qualid(List(Ident("record"))),
        UncurriedTermApplication(
          Qualid(List(Ident("field"))),
          List(Argument(None, Number(3)), Argument(None, Number(7)))
        )
      )
    )
  }

  test("""Testing "record.(@ field nat 7)" """) {
    CoqTermParser("record.(@ field nat 7)") should parse(
      ExplicitApplicationProjection(
        Qualid(List(Ident("record"))),
        ExplicitQualidApplication(Qualid(List(Ident("field"))), List(Qualid(List(Ident("nat"))), Number(7)))
      )
    )
  }

  test("""Testing "aFunction 3 (record.(f) (7 :: nil))" """) {
    CoqTermParser("aFunction 3 (record.(f) (7 :: nil))") should parse(
      UncurriedTermApplication(
        Qualid(List(Ident("aFunction"))),
        List(
          Argument(None, Number(3)),
          Argument(
            None,
            BetweenParenthesis(
              UncurriedTermApplication(
                SimpleProjection(Qualid(List(Ident("record"))), Qualid(List(Ident("f")))),
                List(Argument(None, BetweenParenthesis(InfixOperator(Number(7), "::", Qualid(List(Ident("nil")))))))
              )
            )
          )
        )
      )
    )
  }

  test("""Testing "aFunction 3 (record.(f (7 :: nil)))" """) {
    CoqTermParser("aFunction 3 (record.(f (7 :: nil)))") should parse(
      UncurriedTermApplication(
        Qualid(List(Ident("aFunction"))),
        List(
          Argument(None, Number(3)),
          Argument(
            None,
            BetweenParenthesis(
              ApplicationProjection(
                Qualid(List(Ident("record"))),
                UncurriedTermApplication(
                  Qualid(List(Ident("f"))),
                  List(Argument(None, BetweenParenthesis(InfixOperator(Number(7), "::", Qualid(List(Ident("nil")))))))
                )
              )
            )
          )
        )
      )
    )
  }

  test("""Testing "anIdentifier" """) {
    CoqTermParser("anIdentifier") should parse(Qualid(List(Ident("anIdentifier"))))
  }

  test("""Testing "a.qualified.Identifier" """) {
    CoqTermParser("a.qualified.Identifier") should parse(
      Qualid(List(Ident("a"), Ident("qualified"), Ident("Identifier")))
    )
  }

  test("""Testing "Prop" """) {
    CoqTermParser("Prop") should parse(Prop)
  }

  test("""Testing "Set" """) {
    CoqTermParser("Set") should parse(Set)
  }

  test("""Testing "Type" """) {
    CoqTermParser("Type") should parse(Type)
  }

  test("""Testing "37" """) {
    CoqTermParser("37") should parse(Number(37))
  }

  test("""Testing "true" """) {
    CoqTermParser("true") should parse(Qualid(List(Ident("true"))))
  }

  test("""Testing "(7)" """) {
    CoqTermParser("(7)") should parse(BetweenParenthesis(Number(7)))
  }

  test("""Testing "(3, 7)" """) {
    CoqTermParser("(3, 7)") should parse(TupleValue(List(Number(3), Number(7))))
  }
}
