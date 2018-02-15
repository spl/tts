import data.multiset

namespace multiset -------------------------------------------------------------

variables {α : Type*} {β : Type*} {γ : Type*} [decidable_eq α]

@[simp] theorem disjoint_union_left {s t u : multiset α} :
  disjoint (s ∪ t) u ↔ disjoint s u ∧ disjoint t u :=
begin
  simp [disjoint],
  split,
  begin
    exact λ f, ⟨λ _ p q, f (or.inl p) q, λ _ p q, f (or.inr p) q⟩
  end,
  begin
    intros f _ p q,
    cases p with p p,
    { exact f.1 p q },
    { exact f.2 p q }
  end
end

@[simp] theorem disjoint_union_right {s t u : multiset α} :
  disjoint s (t ∪ u) ↔ disjoint s t ∧ disjoint s u :=
disjoint_comm.trans $ by simp

@[simp] theorem disjoint_ndinsert_left {a : α} {s t : multiset α} :
  disjoint (ndinsert a s) t ↔ a ∉ t ∧ disjoint s t :=
iff.trans (by simp [disjoint]) disjoint_cons_left

@[simp] theorem disjoint_ndinsert_right {a : α} {s t : multiset α} :
  disjoint s (ndinsert a t) ↔ a ∉ s ∧ disjoint s t :=
disjoint_comm.trans $ by simp

end /- namespace -/ multiset ---------------------------------------------------
