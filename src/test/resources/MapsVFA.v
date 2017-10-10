
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.


Definition total_map (A:Type) : Type := nat -> A.


Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A:Type} (m : total_map A)
                    (x : nat) (v : A) : total_map A :=
  fun x1 => if x =? x1 then v else m x1.


Definition examplemap :=
  t_update (t_update (t_empty false) 1 false) 3 true.

