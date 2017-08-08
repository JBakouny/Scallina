(*
Inspired from:
https://www.cs.princeton.edu/~appel/vfa/SearchTree.html

*)

Require Import Coq.Arith.Arith.

Inductive tree V : Type :=
 | E (default : V): tree V
 | T (l: tree V) (key: nat) (value: V) (r: tree V): tree V.

Arguments E {V} _.
Arguments T {V} _ _ _ _.

Definition empty_tree {V} (default: V) := E default.

Fixpoint lookup {V} (x: nat) (t : tree V) : V :=
  match t with
  | E default => default
  | T tl k v tr => if x <? k then lookup x tl 
                         else if k <? x then lookup x tr
                         else v
  end.

Fixpoint insert {V} (x: nat) (v: V) (s: tree V) : tree V :=
 match s with 
 | E dflt => T (E dflt) x v (E dflt)
 | T a y v2 b => if  x <? y then T (insert x v a) y v2 b
                        else if y <? x then T a y v2 (insert x v b)
                        else T a x v b
 end.

Fixpoint elements_aux {V} (s: tree V) (base: list (nat * V)) : list (nat * V) :=
 match s with
 | E _ => base
 | T a k v b => elements_aux a ((k,v) :: elements_aux b base)
 end.

Definition elements {V} (s: tree V) : list (nat * V) := elements_aux s nil.

