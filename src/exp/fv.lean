import .core

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {v : V} -- Variable names
variables {x y : tagged V} -- Variables
variables {ea eb ed ef : exp V} -- Expressions

variables [decidable_eq V]

open occurs

-- Properties of fv

@[simp]
lemma fv_var_bound : x ∉ fv (var bound y) :=
  finset.not_mem_empty x

@[simp]
lemma fv_var_free : x ∉ fv (var free y) ↔ x ≠ y :=
  ⟨ finset.not_mem_singleton.mp
  , λ (p : x ≠ y) (h : x ∈ {y}),
    absurd (finset.mem_of_mem_insert_of_ne h p) (finset.not_mem_empty x)
  ⟩

@[simp]
lemma fv_app : x ∉ fv (app ef ea) ↔ x ∉ fv ef ∧ x ∉ fv ea :=
  finset.not_mem_union

@[simp]
lemma fv_lam : x ∉ fv (lam v eb) ↔ x ∉ fv eb :=
  ⟨by rw fv; exact id, by rw fv; exact id⟩

@[simp]
lemma fv_let_ : x ∉ fv (let_ v ed eb) ↔ x ∉ fv ed ∧ x ∉ fv eb :=
  finset.not_mem_union

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
