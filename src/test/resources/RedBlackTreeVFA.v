(*
From Software Foundations, volume 3:
Verified Functional Algorithms (VFA) by Andrew W. Appel.

Redblack Tree:
https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html

Changes to the original code:
- Replace "int" by "Z" since it is extracted to BigInt in Scala,
see the first alternative in the VFA Extract.v file for more info.
- As a consequence, replace the function "ltb" on "int" by the corresponding "<?" notation for "Z".
- Replace "Variable V : Type." with an implicit parameter "{V}".
- Replace "Variable default: V." with an explicit "(default : V)" parameter.
- Remove "Section TREES" from this file: keep it in the proof file 
- Modify the syntax of the "tree" inductive to add explicit parameter names for "T" nodes.
- Use "Arguments" commands to make the "V" parameter implicit for the "tree" inductive body items 
- Remove the "empty_tree" function since it is just an alias for "E".
- Add type information to all function parameters.
- Add function return types.
- Split the implementation and its proof into two distinct files.
- Replace "Require Import" by "Require Export" since some libraries are used in the proof file.
*)

Require Export Coq.Lists.List.
Export ListNotations.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export ZArith.
Open Scope Z_scope.

Definition key : Set := Z.

Inductive color := Red | Black.

Inductive tree V : Type :=
| E
| T(c: color) (l: tree V) (k: key) (value: V) (r: tree V).

Arguments E {V}.
Arguments T {V} _ _ _ _ _.

Fixpoint lookup {V} (default: V) (x: key) (t : tree V) : V :=
  match t with
  | E => default
  | T _ tl k v tr => if (x <? k) then lookup default x tl 
                         else if (k <? x) then lookup default x tr
                         else v
  end.

Definition balance {V} (rb : color) (t1: tree V) (k : key) (vk: V) (t2: tree V) : tree V:=
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
  | E => E
  | T _ a x vx b => T Black a x vx b
  end.

Fixpoint ins {V} (x : key) (vx: V) (s: tree V) : tree V :=
 match s with 
 | E => T Red E x vx E
 | T c a y vy b => if (x <? y) then balance c (ins x vx a) y vy b
                        else if (y <? x) then balance c a y vy (ins x vx b)
                        else T c a x vx b
 end.

Definition insert {V} (x : key) (vx : V) (s : tree V) : tree V := makeBlack (ins x vx s).