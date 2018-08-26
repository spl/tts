import data.finset

namespace finset ---------------------------------------------------------------
variables {α : Type*} [decidable_eq α] {s s₁ s₂ s₃ : finset α} {a : α}

@[simp]
theorem multiset_disjoint_zero {l : multiset α} : multiset.disjoint l 0 :=
  by rw [multiset.disjoint_comm]; exact multiset.zero_disjoint l

end /- namespace -/ finset -----------------------------------------------------
