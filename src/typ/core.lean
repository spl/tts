import data.finset
import data.fresh
import data.list.extra
import occurs

namespace tts ------------------------------------------------------------------

-- Grammar of types.
@[derive decidable_eq]
inductive typ (V : Type) : Type
  | var : occurs → tagged V → typ -- variable, bound or free
  | arr : typ → typ → typ         -- function arrow

variables {V : Type} -- Type of variable names

namespace typ ------------------------------------------------------------------
variables [_root_.decidable_eq V]

open occurs

protected
def repr [has_repr V] : typ V → string
  | (var bound x)  := _root_.repr x.tag ++ "⟨" ++ _root_.repr x.val ++ "⟩"
  | (var free x)   := _root_.repr x
  | (arr t₁ t₂)    := "(" ++ t₁.repr ++ ") → (" ++ t₂.repr ++ ")"

instance [has_repr V] : has_repr (typ V) :=
⟨typ.repr⟩

-- Free variables of a type
def fv : typ V → finset (tagged V)
  | (var bound _) := ∅
  | (var free x)  := {x}
  | (arr t₁ t₂)   := fv t₁ ∪ fv t₂

-- Free variables of a list of types
def fv_list : list (typ V) → finset (tagged V)
  | []        := ∅
  | (t :: ts) := fv t ∪ fv_list ts

-- Substitute a free variable for a type in a type
def subst (x : tagged V) (t : typ V) : typ V → typ V
  | (var bound y)  := var bound y
  | (var free y)   := if x = y then t else var free y
  | (arr t₁ t₂)    := arr (subst t₁) (subst t₂)

-- Substitute a list of free variables for a list of types in a type
def subst_list : list (tagged V) → list (typ V) → typ V → typ V
  | (x :: xs) (t₂ :: ts₂) t₁ := subst_list xs ts₂ (subst x t₂ t₁)
  | _         _           t₁ := t₁

-- Open a type with a list of types for bound variables.
@[simp]
def open_typs (ts : list (typ V)) : typ V → typ V
  | (var bound x) := (ts.nth x.tag).get_or_else (var bound x)
  | (var free x)  := var free x
  | (arr t₁ t₂)   := arr (open_typs t₁) (open_typs t₂)

-- Open a type with a list of free variables for bound variables.
def open_vars (xs : list (tagged V)) (t : typ V) : typ V :=
  open_typs (list.map (var free) xs) t

-- Property of a locally-closed type.
inductive lc : typ V → Prop
  | var : Π (x : tagged V),                  lc (var free x)
  | arr : Π {t₁ t₂ : typ V}, lc t₁ → lc t₂ → lc (arr t₁ t₂)

-- Locally-closed body of a type scheme with a given arity
def lc_body (n : ℕ) (t : typ V) : Prop :=
  ∃ (L : finset (tagged V)),
  ∀ {xs : list (tagged V)},
  xs.nodup →
  xs.length = n →
  (∀ {x : tagged V}, x ∈ xs → x ∉ L) →
  lc (open_vars xs t)

end /- namespace -/ typ --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
