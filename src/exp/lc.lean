import .core

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables [decidable_eq V]
variables {v : V} -- Variable names
variables {x : tagged V} -- Variables
variables {ea eb ed ef : exp V} -- Expressions

open occurs

@[simp]
theorem lc_var (x : tagged V) : lc (var free x) :=
  lc.var x

@[simp]
theorem lc_app : lc (app ef ea) ↔ lc ef ∧ lc ea :=
  ⟨ λ l, by cases l with _ _ _ l₁ l₂; exact ⟨l₁, l₂⟩
  , λ ⟨l₁, l₂⟩, lc.app l₁ l₂
  ⟩

@[simp]
theorem lc_lam : lc (lam v eb) ↔ lc_body eb :=
  ⟨ λ l, by cases l; apply exists.intro; assumption; assumption
  , λ l, by cases l; apply lc.lam; assumption; assumption
  ⟩

@[simp]
theorem lc_let_ : lc (let_ v ed eb) ↔ lc ed ∧ lc_body eb :=
  ⟨ λ l, by cases l; exact ⟨by assumption, ⟨by assumption, by assumption⟩⟩
  , by rintro ⟨_, _, _⟩; apply lc.let_; repeat {assumption}
  ⟩

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
