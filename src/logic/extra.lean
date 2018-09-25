variables {p : Prop} [decidable p] {α β : Type} {a b : α}

/-
@[simp]
theorem if_branches_eq (a : α) : ite p a a = a :=
  by by_cases h : p; simp [h]
-/

theorem if_distrib (f : α → β) : f (ite p a b) = ite p (f a) (f b) :=
  by by_cases h : p; simp [h]

theorem dif_distrib (f : α → β) : f (dite p (λ h, a) (λ h, b)) = dite p (λ h, f a) (λ h, f b) :=
  by by_cases h : p; simp [h]

@[simp]
theorem decidable_of_decidable_of_iff_refl
: ∀ (d : decidable p), decidable_of_decidable_of_iff d (iff.refl p) = d
  | (is_true _)  := rfl
  | (is_false _) := rfl
