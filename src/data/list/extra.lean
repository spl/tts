import data.list.basic

namespace list -----------------------------------------------------------------
variables {α : Type} {a a₁ a₂ : α} {l l₁ l₂ : list α} {n : ℕ} {p : α → Prop}

theorem nth_of_map {f : α → α} (p : f a = a)
: ∀ {l n}, option.get_or_else ((nth l n).map f) a = f (option.get_or_else (nth l n) a)
  | []       n     := by simp [option.get_or_else, p]
  | (hd::tl) 0     := by simp [option.get_or_else]
  | (hd::tl) (n+1) := by simp [option.get_or_else, nth_of_map]

end /- namespace -/ list -------------------------------------------------------
