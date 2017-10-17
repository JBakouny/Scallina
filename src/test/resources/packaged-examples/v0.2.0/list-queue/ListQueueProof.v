Load ListQueueParam.


(*
Install the paramcoq plugin to run this code:
*)
Add LoadPath "~/paramcoq/src".
Add LoadPath "~/paramcoq/test-suite".

Require Import Parametricity.

Parametricity Recursive nat.

Print nat_R.

Lemma nat_R_equal : 
  forall x y, nat_R x y -> x = y.
intros x y H; induction H; subst; trivial.
Defined.
Lemma equal_nat_R : 
  forall x y, x = y -> nat_R x y.
intros x y H; subst.
induction y; constructor; trivial.
Defined.

Parametricity Recursive option.

Lemma option_nat_R_equal : 
  forall x y, option_R nat nat nat_R x y -> x = y.
intros x1 x2 H; destruct H as [x1 x2 x_R | ].
rewrite (nat_R_equal _ _ x_R); reflexivity.
reflexivity.
Defined.
Lemma equal_option_nat_R : 
  forall x y, x = y -> option_R nat nat nat_R x y.
intros x y H; subst.
destruct y; constructor; apply equal_nat_R; reflexivity.
Defined.

Parametricity Recursive prod.
Parametricity Recursive Queue.

Print Queue_R.
Check Queue_R.

Notation Bisimilar := Queue_R.

Print Queue_R.


Definition R (l1 : list nat) (l2 : list nat * list nat) :=
 let (back, front) := l2 in 
  l1 = back ++ rev front.

Lemma rev_app : 
  forall A (l1 l2 : list A), 
    rev (l1 ++ l2) = rev l2 ++ rev l1.
induction l1.
intro; symmetry; apply app_nil_r.
intro; simpl; rewrite IHl1; rewrite app_ass.
reflexivity.
Defined.

Lemma rev_list_rect A  :
      forall P:list A-> Type,
	P nil ->
	(forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
	forall l:list A, P (rev l).
Proof.
  induction l; auto.
Defined.

Theorem rev_rect A :
  forall P:list A -> Type,
	P nil ->
	(forall (x:A) (l:list A), P l -> P (l ++ x :: nil)) ->
  forall l:list A, P l.
Proof.
  intros.
  generalize (rev_involutive l).
  intros E; rewrite <- E.
  apply (rev_list_rect _ P).
  auto.

  simpl.
  intros.
  apply (X0 a (rev l0)).
  auto.
Defined.


Lemma bisim_list_dlist : Bisimilar ListQueue DListQueue.
apply (Queue_R_Build_Queue_R _ _ R).

* reflexivity.

* intros n1 n2 n_R.
pose (nat_R_equal _ _ n_R) as H.
destruct H. clear n_R.
intros l [back front].
unfold R.
simpl.
intro; subst.
simpl.
reflexivity.

* intros l  [back front].
generalize l. clear l.
unfold R; fold R.
pattern back.

apply rev_rect.

intros l H; subst.
rewrite rev_app.
simpl.
rewrite app_nil_r.
rewrite rev_involutive.

destruct front.
constructor.
repeat constructor.
apply equal_nat_R; reflexivity.

clear back; intros hd back IHR l H.
subst.
rewrite rev_app.
rewrite rev_involutive.
rewrite rev_app.
simpl.
destruct front.
simpl.
repeat constructor.
apply equal_nat_R; reflexivity.
simpl.
repeat constructor.
apply equal_nat_R; reflexivity.
unfold R.
rewrite rev_app.
simpl.
rewrite rev_involutive.
reflexivity.
Defined.

Print program.
Check program.
Parametricity Recursive program.
Check program_R.

Lemma program_independent : 
 forall n, 
  program ListQueue n = program DListQueue n.
intro n.
apply option_nat_R_equal.
apply program_R.
apply bisim_list_dlist.
apply equal_nat_R.
reflexivity.
Defined.
Print program.
Print program_R.
*)