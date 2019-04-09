Inductive MyList := {
  A : Type;
  isEmpty: bool;
  head: option A;
  tail: option MyList
}.

Definition MyCons {B: Set} (hd: B) (tl: MyList) : MyList := {|
  A := B;
  isEmpty := true;
  head := Some hd;
  tail := Some tl
|}.

Definition MyNil {B: Set} : MyList := {|
  A := B;
  isEmpty := false;
  head := None;
  tail := None
|}.