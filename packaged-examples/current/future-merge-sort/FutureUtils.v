

Inductive Future A :=
future (value : A).

Arguments future {A} _.

Definition getValue {A} (fv: Future A) : A :=
match fv with
  future v => v
end.

Definition fut_flat_map {A B} (f: A -> Future B) (fv: Future A) : Future B :=
match fv with
  future v => f v
end.

Definition fut_map {A B} (f: A -> B) (fv: Future A) : Future B :=
match fv with
  future v => future (f v)
end.


