(*
From Coq's standard library - Natural Numbers:
https://github.com/coq/coq/blob/v8.9/theories/Init/Nat.v

Changes to the original code:
- Replace 0 by Zero.
- Replace ' by 1 in qualids.
- Inline notations.
- Add type information to all function parameters.
- Add function return types.
*)

Inductive Nat := Zero | S (n : Nat).

Definition t : Set := Nat.

Definition zero : Nat := Zero.
Definition one : Nat := S Zero.
Definition two : Nat := S (S Zero).

Definition succ : Nat -> Nat := S.

Definition pred (n : Nat) : Nat :=
  match n with
    | Zero => n
    | S u => u
  end.

Fixpoint add (n m : Nat) : Nat :=
  match n with
  | Zero => m
  | S p => S (add p m)
  end.

Definition double (n : Nat) : Nat := add n n.

Fixpoint mul (n m : Nat) : Nat :=
  match n with
  | Zero => Zero
  | S p => add m (mul p m)
  end.

Fixpoint sub (n m : Nat) : Nat :=
  match n, m with
  | S k, S l => sub k l
  | _, _ => n
  end.

Fixpoint eqb (n m : Nat) : bool :=
  match n, m with
    | Zero, Zero => true
    | Zero, S _ => false
    | S _, Zero => false
    | S n1, S m1 => eqb n1 m1
  end.

Fixpoint leb (n m : Nat) : bool :=
  match n, m with
    | Zero, _ => true
    | _, Zero => false
    | S n1, S m1 => leb n1 m1
  end.

Definition ltb (n m : Nat) := leb (S n) m.

Fixpoint compare (n m : Nat) : comparison :=
  match n, m with
   | Zero, Zero => Eq
   | Zero, S _ => Lt
   | S _, Zero => Gt
   | S n1, S m1 => compare n1 m1
  end.


Fixpoint max (n m : Nat) : Nat :=
  match n, m with
    | Zero, _ => m
    | S n1, Zero => n
    | S n1, S m1 => S (max n1 m1)
  end.

Fixpoint min (n m : Nat) : Nat :=
  match n, m with
    | Zero, _ => Zero
    | S n1, Zero => Zero
    | S n1, S m1 => S (min n1 m1)
  end.

Fixpoint even (n : Nat) : bool :=
  match n with
    | Zero => true
    | S Zero => false
    | S (S n1) => even n1
  end.

Definition odd (n : Nat) : bool := negb (even n).

Fixpoint pow (n m : Nat) : Nat :=
  match m with
    | Zero => S Zero
    | S m => mul n (pow n m)
  end.

Fixpoint tail_add (n m : Nat) : Nat :=
  match n with
    | Zero => m
    | S n => tail_add n (S m)
  end.

Fixpoint tail_addmul (r n m : Nat) : Nat :=
  match n with
    | Zero => r
    | S n => tail_addmul (tail_add m r) n m
  end.

Definition tail_mul (n m : Nat) : Nat := tail_addmul Zero n m.

(* Disregard the following functions since they use
Decimals which are not currently supported by Scallina:
- of_uint_acc
- of_uint
- to_little_uint
- to_uint
- of_int
- to_int
*)

Fixpoint divmod (x y q u : Nat) : Nat * Nat :=
  match x with
    | Zero => (q,u)
    | S x1 => match u with
                | Zero => divmod x1 y (S q) y
                | S u1 => divmod x1 y q u1
              end
  end.

Definition div (x y : Nat) : Nat :=
  match y with
    | Zero => y
    | S y1 => fst (divmod x y1 Zero y1)
  end.

Definition modulo (x y : Nat) :=
  match y with
    | Zero => y
    | S y1 => sub y1 (snd (divmod x y1 Zero y1))
  end.

Fixpoint gcd (a b : Nat) : Nat :=
  match a with
   | Zero => b
   | S a1 => gcd (modulo b (S a1)) (S a1)
  end.

Definition square (n : Nat) : Nat := mul n n.

Fixpoint sqrt_iter (k p q r : Nat) : Nat :=
  match k with
    | Zero => p
    | S k1 => match r with
                | Zero => sqrt_iter k1 (S p) (S (S q)) (S (S q))
                | S r1 => sqrt_iter k1 p q r1
              end
  end.

Definition sqrt (n : Nat) : Nat := sqrt_iter n Zero Zero Zero.


Fixpoint log2_iter (k p q r : Nat) : Nat :=
  match k with
    | Zero => p
    | S k1 => match r with
                | Zero => log2_iter k1 (S p) (S q) q
                | S r1 => log2_iter k1 p (S q) r1
              end
  end.

Definition log2 (n : Nat) : Nat := log2_iter (pred n) Zero (S Zero) Zero.

(* Replace iter by a version that does not use the dependently typed nat_rect function, see the result of "Extraction iter" for OCaml *)
Fixpoint iter {A} (n:Nat) (f:A->A) (x:A) : A :=
 match n with
  | Zero => x
  | S n0 => f (iter n0 f x)
 end.

Fixpoint div2 (n : Nat) : Nat :=
  match n with
  | Zero => Zero
  | S Zero => Zero
  | S (S n1) => S (div2 n1)
  end.

Fixpoint testbit (a n : Nat) : bool :=
 match n with
   | Zero => odd a
   | S n => testbit (div2 a) n
 end.


(* Replace shiftl by a version that does not use the dependently typed nat_rect function, see the result of "Extraction iter" for OCaml *)
Fixpoint shiftl (a n: Nat) : Nat :=
 match n with
   | Zero => a
   | S n0 => double (shiftl a n0)
 end.

(* Replace shiftr by a version that does not use the dependently typed nat_rect function, see the result of "Extraction iter" for OCaml *)
Fixpoint shiftr (a n: Nat) : Nat :=
 match n with
   | Zero => a
   | S n0 => div2 (shiftr a n0)
 end.

Fixpoint bitwise (op:bool->bool->bool) (n a b : Nat) : Nat :=
 match n with
  | Zero => Zero
  | S n1 =>
    add (if op (odd a) (odd b) then (S Zero) else Zero)
    (mul (S (S Zero)) (bitwise op n1 (div2 a) (div2 b)))
 end.

Definition land (a b : Nat) : Nat := bitwise andb a a b.
Definition lor (a b : Nat) : Nat := bitwise orb (max a b) a b.
Definition ldiff (a b : Nat) : Nat := bitwise (fun b b1 => andb b (negb b1)) a a b.
Definition lxor (a b : Nat) : Nat := bitwise xorb (max a b) a b.

