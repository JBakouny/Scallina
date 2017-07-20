fix rightMost {A : Type} (t : BinTree) : A := match t with
  L x => x
| N l r => rightMost r
end
