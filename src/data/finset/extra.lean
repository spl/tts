import data.finset

namespace finset ---------------------------------------------------------------

variables {A : Type} [decidable_eq A] {a b : A} {s s₁ s₂ : finset A}

theorem ne_of_mem_of_not_mem (pa : a ∈ s) (pb : b ∉ s) : a ≠ b :=
  ne_of_mem_erase (@@eq.substr _ (erase_insert pb) pa)

theorem not_mem_singleton : a ∉ singleton b ↔ a ≠ b :=
  ⟨ λ p, ne.symm (ne_of_mem_of_not_mem (mem_singleton_self b) p)
  , λ p q, absurd (mem_singleton.mp q) p
  ⟩

theorem not_mem_union : a ∉ s₁ ∪ s₂ ↔ a ∉ s₁ ∧ a ∉ s₂ :=
  ⟨ λ h₁ : a ∉ s₁ ∪ s₂,
    ⟨ λ h₂ : a ∈ s₁, absurd (finset.mem_union_left s₂ h₂) h₁
    , λ h₂ : a ∈ s₂, absurd (finset.mem_union_right s₁ h₂) h₁
    ⟩
  , λ (h₁ : a ∉ s₁ ∧ a ∉ s₂) (h₂ : a ∈ s₁ ∪ s₂),
    absurd (finset.mem_union.mp h₂)
           ((decidable.not_or_iff_and_not (a ∈ s₁) (a ∈ s₂)).mpr h₁)
  ⟩

class has_fresh (A : Type) :=
  (fresh : ∀ (s : finset A), Σ' a : A, a ∉ s)

-- Given `F : finset A` of `A` elements, produce a fresh `a : A` and a proof
-- that `a` is not a member of `F`.
def fresh {A : Type} [has_fresh A] (s : finset A) : Σ' (a : A), a ∉ s :=
  has_fresh.fresh s

end /- namespace -/ finset -----------------------------------------------------
