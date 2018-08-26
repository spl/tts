import data.list.basic

namespace list -----------------------------------------------------------------
variables {α : Type} {a a₁ a₂ : α} {l l₁ l₂ : list α} {n : ℕ} {p : α → Prop}

theorem nth_of_map {f : α → α} (p : f a = a)
: ∀ {l n}, option.get_or_else ((nth l n).map f) a = f (option.get_or_else (nth l n) a)
  | []       n     := by simp [option.get_or_else, p]
  | (hd::tl) 0     := by simp [option.get_or_else]
  | (hd::tl) (n+1) := by simp [option.get_or_else, nth_of_map]

theorem append_cons_left : l₁ ++ a :: l₂ = l₁ ++ [a] ++ l₂ :=
  by induction l₁; simp

theorem length_tail_eq_length_tail
{α β : Type} {a : α} {b : β} {la : list α} {lb : list β}
: length (a :: la) = length (b :: lb) → length la = length lb :=
  by simp [length]; exact nat.add_left_cancel

end /- namespace -/ list -------------------------------------------------------
