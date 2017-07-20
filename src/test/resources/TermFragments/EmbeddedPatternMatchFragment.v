match k with
  0 => None
| S k1 =>
  match n with
    0 => Some 0
  | 1 => Some 1
  | n => None
  end
end
