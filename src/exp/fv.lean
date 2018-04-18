import .defs

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} [decidable_eq V] -- Type of variable names

-- Properties of fv

lemma fv.not_mem_varf {x y : V} : x ∉ fv (varf y) ↔ x ≠ y :=
  ⟨ λ p : x ∉ {y},
    finset.not_mem_singleton.mp p
  , λ (p : x ≠ y) (h : x ∈ {y}),
    absurd (finset.mem_of_mem_insert_of_ne h p) (finset.not_mem_empty x)
  ⟩

lemma fv.app {x : V} {ef ea : exp V} : x ∉ fv (app ef ea) ↔ x ∉ fv ef ∧ x ∉ fv ea :=
  finset.not_mem_union

lemma fv.lam {x : V} {eb : exp V} : x ∉ fv (lam eb) ↔ x ∉ fv eb :=
  ⟨by rw fv; exact id, by rw fv; exact id⟩

lemma fv.let_ {x : V} {ed eb : exp V} : x ∉ fv (let_ ed eb) ↔ x ∉ fv ed ∧ x ∉ fv eb :=
  finset.not_mem_union

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
