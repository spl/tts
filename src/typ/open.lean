import .core

namespace tts ------------------------------------------------------------------
namespace typ ------------------------------------------------------------------
variables {i : ℕ} -- Natural numbers
variables {V : Type} -- Type of variable names
variables {x : V} -- Variable names
variables {t t₁ t₂ : typ V} -- Types
variables {ts : list (typ V)} -- Lists of types

-- Opening a locally-closed type is the identity
@[simp]
theorem open_lc (p : lc t) : t.open ts = t :=
  by induction t; cases p; simp [typ.open, *]

end /- namespace -/ typ --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
