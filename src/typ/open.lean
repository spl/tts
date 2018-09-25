import .core

namespace tts ------------------------------------------------------------------
namespace typ ------------------------------------------------------------------
variables {i : ℕ} -- Natural numbers
variables {V : Type} -- Type of variable names
variables [_root_.decidable_eq V]
variables {t : typ V} -- Types
variables {ts : list (typ V)} -- Lists of types


-- Opening a locally-closed type is the identity
@[simp]
theorem open_lc (h : lc t) : open_typs ts t = t :=
  by induction t; cases h; simp [open_typs, *]

end /- namespace -/ typ --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
