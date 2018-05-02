import .core

namespace tts ------------------------------------------------------------------
namespace typ ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {x : V} -- Variable names
variables {t₁ t₂ : typ V} -- Types

@[simp]
theorem lc_varf (x : V) : lc (varf x) :=
  lc.varf x

@[simp]
theorem lc_arr : lc (arr t₁ t₂) ↔ lc t₁ ∧ lc t₂ :=
  ⟨ λ l, by cases l with _ _ _ l₁ l₂; exact ⟨l₁, l₂⟩
  , λ ⟨l₁, l₂⟩, lc.arr l₁ l₂
  ⟩

end /- namespace -/ typ --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
