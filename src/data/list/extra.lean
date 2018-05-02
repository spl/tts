import data.list.basic

namespace list -----------------------------------------------------------------
variables {α : Type} {a a₁ a₂ : α} {l l₁ l₂ : list α} {n : ℕ} {p : α → Prop}

theorem nth_of_map {f : α → α} (p : f a = a)
: option.get_or_else (nth (map f l) n) a = f (option.get_or_else (nth l n) a) :=
  by induction l generalizing n; [skip, cases n]; simp [*, option.get_or_else]

theorem append_cons_left : l₁ ++ a :: l₂ = l₁ ++ [a] ++ l₂ :=
  by induction l₁; simp

theorem length_tail_eq_length_tail
{α β : Type} {a : α} {b : β} {la : list α} {lb : list β}
: length (a :: la) = length (b :: lb) → length la = length lb :=
  by simp [length]; exact nat.add_left_cancel

theorem forall_mem_singleton {p : α → Prop} {a : α} (h : p a) : ∀ x ∈ [a], p x :=
  λ x p, (mem_singleton.mp p).symm ▸ h

theorem forall_mem_append {p : α → Prop} {l₁ l₂ : list α}
: (∀ x ∈ l₁ ++ l₂, p x) ↔ (∀ x ∈ l₁, p x) ∧ (∀ x ∈ l₂, p x) :=
  by simp [or_imp_distrib, forall_and_distrib]

end /- namespace -/ list -------------------------------------------------------
