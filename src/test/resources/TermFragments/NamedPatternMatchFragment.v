match Node (Node Leaf Leaf) (Node Leaf Leaf) as c with
  Leaf  => Leaf
| c => Node Leaf Leaf
end