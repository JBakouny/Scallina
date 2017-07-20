match Node (Node Leaf Leaf) Leaf, Leaf with
  Leaf, Leaf  => Leaf
| Node l r, Leaf => l
| Leaf, Node l r => r
| Node l _, Node _ r => Node l r
end