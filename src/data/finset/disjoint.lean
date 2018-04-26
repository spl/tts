import data.finset

namespace finset ---------------------------------------------------------------
variables {α : Type*} [decidable_eq α] {s s₁ s₂ s₃ : finset α} {a : α}

def disjoint (s₁ s₂ : finset α) : Prop :=
  s₁ ∩ s₂ = ∅

local attribute [simp] disjoint inter_eq_empty_iff_disjoint mem_def

@[simp]
theorem disjoint_empty_left : disjoint ∅ s ↔ true :=
  by simp

@[simp]
theorem disjoint_empty_right : disjoint s ∅ ↔ true :=
  by simp

theorem disjoint_comm : disjoint s₁ s₂ ↔ disjoint s₂ s₁ :=
  by simp

@[simp]
theorem multiset_disjoint_zero {l : multiset α} : multiset.disjoint l 0 :=
  by rw [multiset.disjoint_comm]; exact multiset.zero_disjoint l

@[simp]
theorem disjoint_singleton_left : disjoint (singleton a) s ↔ a ∉ s :=
  by simp

@[simp]
theorem disjoint_singleton_right : disjoint s (singleton a) ↔ a ∉ s :=
  by simp

@[simp]
theorem disjoint_insert_right : disjoint s₁ (insert a s₂) ↔ a ∉ s₁ ∧ disjoint s₁ s₂ :=
  by simp

@[simp]
theorem disjoint_insert_left : disjoint (insert a s₁) s₂ ↔ a ∉ s₂ ∧ disjoint s₁ s₂ :=
  by simp

@[simp]
theorem disjoint_union_left : disjoint (s₁ ∪ s₂) s₃ ↔ disjoint s₁ s₃ ∧ disjoint s₂ s₃ :=
  by simp

@[simp]
theorem disjoint_union_right : disjoint s₁ (s₂ ∪  s₃) ↔ disjoint s₁ s₂ ∧ disjoint s₁ s₃ :=
  by simp

end /- namespace -/ finset -----------------------------------------------------
