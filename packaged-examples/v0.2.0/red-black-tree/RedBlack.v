
(*
From Software Foundations, volume 3:
Verified Functional Algorithms by Andrew W. Appel.

Inspired from red black tree:
https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html

*)


Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Inductive color := Red | Black.

Inductive tree V : Type :=
| E(default: V) : tree V 
| T(c: color) (l: tree V) (key: Z) (value: V) (r: tree V): tree V.

Arguments E {V} _.
Arguments T {V} _ _ _ _ _.

Definition empty_tree {V} (default: V) := E default.

Fixpoint lookup {V} (x: Z) (t : tree V) : V :=
  match t with
  | E default => default
  | T _ tl k v tr => if (x <? k) then lookup x tl 
                         else if (k <? x) then lookup x tr
                         else v
  end.

Definition balance {V} (rb : color) (t1: tree V) (k : Z) (vk: V) (t2: tree V) : tree V:=
 match rb with Red => T Red t1 k vk t2
 | _ => 
 match t1 with 
 | T Red (T Red a x vx b) y vy c =>
      T Red (T Black a x vx b) y vy (T Black c k vk t2)
 | T Red a x vx (T Red b y vy c) =>
      T Red (T Black a x vx b) y vy (T Black c k vk t2)
 | a => match t2 with 
            | T Red (T Red b y vy c) z vz d =>
	        T Red (T Black t1 k vk b) y vy (T Black c z vz d)
            | T Red b y vy (T Red c z vz d)  =>
	        T Red (T Black t1 k vk b) y vy (T Black c z vz d)
            | _ => T Black t1 k vk t2
            end
  end
 end.

Definition makeBlack {V} (t : tree V) : tree V := 
  match t with 
  | E dflt => E dflt
  | T _ a x vx b => T Black a x vx b
  end.

Fixpoint ins {V} (x : Z) (vx: V) (s: tree V) : tree V :=
 match s with 
 | E dflt => T Red (E dflt) x vx (E dflt)
 | T c a y vy b => if (x <? y) then balance c (ins x vx a) y vy b
                        else if (y <? x) then balance c a y vy (ins x vx b)
                        else T c a x vx b
 end.

Definition insert {V} (x : Z) (vx : V) (s : tree V) : tree V := makeBlack (ins x vx s).
