import .core

namespace tts ------------------------------------------------------------------
namespace typ ------------------------------------------------------------------
variables {V : Type} [_root_.decidable_eq V] -- Type of variable names

open occurs

/-- Open a type with a list of types for bound variables -/
@[simp] def open_typs (ts : list (typ V)) : typ V → typ V
| (var bound x) := (ts.nth x.tag).get_or_else (var bound x)
| (var free x)  := var free x
| (arr t₁ t₂)   := arr (open_typs t₁) (open_typs t₂)

/-- Open a type with a list of free variables for bound variables -/
def open_vars (xs : list (tagged V)) (t : typ V) : typ V :=
open_typs (list.map (var free) xs) t

end /- namespace -/ typ --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
