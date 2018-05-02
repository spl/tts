import typ.core
import data.finset.disjoint_list

namespace tts ------------------------------------------------------------------

-- Grammar of type schemes.
@[derive decidable_eq]
structure sch (V : Type) : Type :=
  (arity : ℕ)
  (type : typ V)

attribute [pp_using_anonymous_constructor] sch

variables {V : Type} -- Type of variable names

namespace sch ------------------------------------------------------------------
variables [_root_.decidable_eq V]

-- Get the free variables of a scheme.
def fv (s : sch V) : finset V :=
  s.type.fv

-- Substitute a free variable for a type in a scheme
def subst (x : V) (t : typ V) (s : sch V) : sch V :=
  ⟨s.arity, typ.subst x t s.type⟩

-- Substitute a list of free variables for a list of types in a scheme
def subst_list (xs : list V) (ts : list (typ V)) (s : sch V) : sch V :=
  ⟨s.arity, typ.subst_list xs ts s.type⟩

end /- namespace -/ sch --------------------------------------------------------

-- Open a type scheme with a list of expressions for bound variables.
-- Note: This definition is defined outside the `sch` namespace because it
-- conflicts with the keyword `open` if declared without the `sch`. prefix.
protected
def sch.open (ts : list (typ V)) (s : sch V) : typ V :=
  s.type.open ts

namespace sch ------------------------------------------------------------------

-- Open a type scheme with a list of free variables for bound variables.
def open_vars (xs : list V) (s : sch V) : typ V :=
  s.type.open_vars xs

variables [_root_.decidable_eq V]

-- Property of a well-formed scheme.
def well_formed (s : sch V) : Prop :=
  ∃ (L : finset V)
  , ∀ {xs : list V}
  , xs.nodup
  → xs.length = s.arity
  → finset.disjoint_list xs L
  → typ.lc (sch.open_vars xs s)

end /- namespace -/ sch --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
