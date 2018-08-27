import .core

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {x y : V} -- Variable names
variables {ea eb ed ef : exp V} -- Expressions

variables [decidable_eq V]

-- Properties of fv

lemma fv_not_mem_varf : x ∉ fv (varf y) ↔ x ≠ y :=
  ⟨ λ p : x ∉ {y},
    finset.not_mem_singleton.mp p
  , λ (p : x ≠ y) (h : x ∈ {y}),
    absurd (finset.mem_of_mem_insert_of_ne h p) (finset.not_mem_empty x)
  ⟩

lemma fv_app : x ∉ fv (app ef ea) ↔ x ∉ fv ef ∧ x ∉ fv ea :=
  finset.not_mem_union

lemma fv_lam : x ∉ fv (lam eb) ↔ x ∉ fv eb :=
  ⟨by rw fv; exact id, by rw fv; exact id⟩

lemma fv_let_ : x ∉ fv (let_ ed eb) ↔ x ∉ fv ed ∧ x ∉ fv eb :=
  finset.not_mem_union

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
