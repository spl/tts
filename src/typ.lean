import .fresh
import .list
import data.finset

namespace tts ------------------------------------------------------------------
variables {V : Type} -- Type of variable names

-- Grammar of types
inductive typ (V : Type) : Type
  | bvar {} : ℕ → typ          -- bound variable
  | fvar    : V → typ          -- free variable
  | arr     : typ → typ → typ  -- function arrow

open typ

-- Open a type with a list of expressions for bound variables
protected
def typ.open (ts : list (typ V)) : typ V → typ V
  | (bvar i)    := (ts.nth i).get_or_else (bvar 0)
  | (fvar x)    := fvar x
  | (arr t₁ t₂) := arr t₁.open t₂.open

-- Open a type with a list of free variables for bound variables
protected
def typ.open_vars (vs : list V) : typ V → typ V :=
  typ.open (vs.map fvar)

namespace typ ------------------------------------------------------------------

-- Property of a locally-closed type
inductive lc : typ V → Prop
  | fvar : Π (x : V),         lc (fvar x)
  | arr  : Π {t₁ t₂ : typ V}, lc (arr t₁ t₂)

def lc_types (n : ℕ) (l : list (typ V)) : Prop :=
  n = l.length ∧ l.all_prop lc

end /- namespace -/ typ --------------------------------------------------------

-- Grammar of type schemes
structure sch (V : Type) : Type :=
  (arity : ℕ)
  (type : typ V)

-- Open a type scheme with a list of expressions for bound variables
protected
def sch.open (ts : list (typ V)) (s : sch V) : typ V :=
  s.type.open ts

-- Open a type scheme with a list of free variables for bound variables
protected
def sch.open_vars (vs : list V) (s : sch V) : typ V :=
  s.type.open_vars vs

namespace sch ------------------------------------------------------------------
variable [has_insert V (finset V)]

-- Property of a scheme body
def body (n : ℕ) (t : typ V) : Prop :=
  ∃ (vs : finset V), ∀ (xs : list V), fresh vs n xs → (t.open_vars xs).lc

-- Property of a well-formed scheme
def well_formed (s : sch V) : Prop :=
  body s.arity s.type

end /- namespace -/ sch --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
