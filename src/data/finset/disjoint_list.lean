import .disjoint
import data.list.to_finset

namespace finset ---------------------------------------------------------------
variables {α : Type*} [decidable_eq α]

def disjoint_list (l : list α) (s : finset α) : Prop :=
  disjoint l.to_finset s

local attribute [simp] disjoint_list

variables {a : α} {l : list α} {s s₁ s₂ : finset α}

@[simp]
theorem disjoint_list_nil : disjoint_list [] s ↔ true :=
  by simp

@[simp]
theorem disjoint_list_cons : disjoint_list (a :: l) s ↔ a ∉ s ∧ disjoint_list l s :=
  by simp

@[simp]
theorem disjoint_list_union : disjoint_list l (s₁ ∪ s₂) ↔ disjoint_list l s₁ ∧ disjoint_list l s₂ :=
  by simp

end /- namespace -/ finset -----------------------------------------------------
