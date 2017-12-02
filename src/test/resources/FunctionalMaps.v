(*
Inspired from:
https://www.seas.upenn.edu/~cis500/current/sf/Maps.html
*)


Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.


Inductive id : Type :=
  | Id(n: nat).

Definition beq_id (id1 id2: id) : bool :=
  match id1,id2 with
    | Id n1, Id n2 => n1 =? n2
  end.

(* ################################################################# *)
(** * Total Maps *)

Definition total_map (A:Type) : Type := id -> A.

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun (x2: id) => if beq_id x x2 then v else m x2.


Definition examplemap :=
  t_update (t_update (t_empty false) (Id 1) false)
           (Id 3) true.

(* ################################################################# *)
(** * Partial maps *)

Definition partial_map (A:Type) : Type := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Definition update {A:Type} (m : partial_map A)
                  (x : id) (v : A) :=
  t_update m x (Some v).
