import data.finset
import data.list.extra

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

-- Free variables of a type
def fv : typ V → finset V
  | (varb i)    := ∅
  | (varf x)    := {x}
  | (arr t₁ t₂) := fv t₁ ∪ fv t₂

-- Free variables of a list of types
def fv_list : list (typ V) → finset V :=
  list.foldr (λ t acc, fv t ∪ acc) ∅

-- Substitute a free variable for a type in a type
def subst (y : V) (t : typ V) : typ V → typ V
  | (varb i)    := varb i
  | (varf x)    := if x = y then t else varf x
  | (arr t₁ t₂) := arr (subst t₁) (subst t₂)

-- Substitute a list of free variables for a list of types in a type
def subst_list : list V → list (typ V) → typ V → typ V
  | (x :: xs) (t₂ :: ts₂) t₁ := subst_list xs ts₂ (subst x t₂ t₁)
  | _         _           t₁ := t₁

end /- namespace -/ typ --------------------------------------------------------

open typ

-- Open a type with a list of expressions for bound variables.
-- Note: This definition is defined with an explicit namespace to avoid conflict
-- with the keyword `open`.
protected
def typ.open (ts : list (typ V)) : typ V → typ V
  | (varb i)    := (ts.nth i).get_or_else (varb 0)
  | (varf x)    := varf x
  | (arr t₁ t₂) := arr t₁.open t₂.open

namespace typ ------------------------------------------------------------------

-- Open a type with a list of free variables for bound variables.
def open_vars (vs : list V) (t : typ V) : typ V :=
  t.open (vs.map varf)

-- Property of a locally-closed type.
inductive lc : typ V → Prop
  | varf : Π (x : V),                         lc (varf x)
  | arr  : Π {t₁ t₂ : typ V}, lc t₁ → lc t₂ → lc (arr t₁ t₂)

end /- namespace -/ typ --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
