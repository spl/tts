import .list
import data.finset

namespace tts ------------------------------------------------------------------

-- Grammar of types.
@[derive decidable_eq]
inductive typ (V : Type) : Type
  | varb {} : ℕ → typ          -- bound variable
  | varf    : V → typ          -- free variable
  | arr     : typ → typ → typ  -- function arrow

variables {V : Type} -- Type of variable names

namespace typ ------------------------------------------------------------------
variables [_root_.decidable_eq V]

-- Get the free variables of a type.
def fv : typ V → finset V
  | (varb i)    := ∅
  | (varf x)    := {x}
  | (arr t₁ t₂) := fv t₁ ∪ fv t₂

-- Substitute a free variable for a type in a type.
def subst (y : V) (t : typ V) : typ V → typ V
  | (varb i)    := varb i
  | (varf x)    := if x = y then t else varf x
  | (arr t₁ t₂) := arr (subst t₁) (subst t₂)

end /- namespace -/ typ --------------------------------------------------------

open typ

-- Open a type with a list of expressions for bound variables.
-- Note: This definition is defined outside the `typ` namespace because it
-- conflicts with the keyword `open` if declared without the `typ`. prefix.
protected
def typ.open (ts : list (typ V)) : typ V → typ V
  | (varb i)    := (ts.nth i).get_or_else (varb 0)
  | (varf x)    := varf x
  | (arr t₁ t₂) := arr t₁.open t₂.open

namespace typ ------------------------------------------------------------------

-- Open a type with a list of free variables for bound variables.
protected
def open_vars (vs : list V) (t : typ V) : typ V :=
  t.open (vs.map varf)

-- Property of a locally-closed type.
inductive lc : typ V → Prop
  | varf : Π (x : V),         lc (varf x)
  | arr  : Π {t₁ t₂ : typ V}, lc (arr t₁ t₂)

def lc_types (n : ℕ) (l : list (typ V)) : Prop :=
  n = l.length ∧ l.all_prop lc

end /- namespace -/ typ --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
