import .core

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {x : V} -- Variable names
variables {ea eb ed ef : exp V} -- Expressions

@[simp]
theorem lc_varf (x : V) : lc (varf x) :=
  lc.varf x

@[simp]
theorem lc_app : lc (app ef ea) ↔ lc ef ∧ lc ea :=
  ⟨ λ l, by cases l with _ _ _ l₁ l₂; exact ⟨l₁, l₂⟩
  , λ ⟨l₁, l₂⟩, lc.app l₁ l₂
  ⟩

@[simp]
theorem lc_lam : lc (lam eb) ↔ lc_body eb :=
  ⟨ λ l, by cases l with _ _ _ _ _ L _ F; exact ⟨L, @F⟩
  , λ ⟨_, F⟩, lc.lam @F
  ⟩

@[simp]
theorem lc_let_ : lc (let_ ed eb) ↔ lc ed ∧ lc_body eb :=
  ⟨ λ l, by cases l with _ _ _ _ _ _ _ _ L _ _ lc_ed lc_eb; exact ⟨lc_ed, L, @lc_eb⟩
  , λ ⟨lc_ed, _, lc_eb⟩, lc.let_ lc_ed @lc_eb
  ⟩

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
