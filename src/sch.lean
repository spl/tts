import .fresh
import .typ

namespace tts ------------------------------------------------------------------

-- Grammar of type schemes.
structure sch (V : Type) : Type :=
  (arity : ℕ)
  (type : typ V)

variables {V : Type} [decidable_eq V] -- Type of variable names

namespace sch ------------------------------------------------------------------

-- Get the free variables of a scheme.
def fv (s : sch V) : finset V :=
  s.type.fv

end /- namespace -/ sch --------------------------------------------------------

-- Open a type scheme with a list of expressions for bound variables.
-- Note: This definition is defined outside the `sch` namespace because it
-- conflicts with the keyword `open` if declared without the `sch`. prefix.
protected
def sch.open (ts : list (typ V)) (s : sch V) : typ V :=
  s.type.open ts

namespace sch ------------------------------------------------------------------

-- Open a type scheme with a list of free variables for bound variables.
protected
def open_vars (vs : list V) (s : sch V) : typ V :=
  s.type.open_vars vs

-- Property of a scheme body.
def body (n : ℕ) (t : typ V) : Prop :=
  ∃ (vs : finset V), ∀ (xs : list V), fresh vs n xs → (t.open_vars xs).lc

-- Property of a well-formed scheme.
def well_formed (s : sch V) : Prop :=
  body s.arity s.type

end /- namespace -/ sch --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
