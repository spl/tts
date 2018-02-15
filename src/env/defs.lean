import sch

namespace tts ------------------------------------------------------------------

-- An environment is an association list of type bindings or pairs of a variable
-- and the variable's type scheme.
@[inline, reducible]
def env (V : Type) : Type :=
  list (V × sch V)

variables {V : Type} -- Type of variable names

namespace env ------------------------------------------------------------------

@[pattern, inline, reducible]
def binding : V → sch V → V × sch V :=
  prod.mk

-- A binding appears somewhere in the environment
def binds (x : V) (s : sch V) (Γ : env V) : Prop :=
  binding x s ∈ Γ

-- A singleton environment
def one (x : V) (s : sch V) : env V :=
  [binding x s]

-- Add a binding to an environment
def add (x : V) (s : sch V) (Γ : env V) : env V :=
   one x s ++ Γ

-- All of the remaining definitions require decidable equality on V
variables [decidable_eq V]

-- Free variables of an environment
def fv : env V → finset V
  | []                 := ∅
  | (binding _ s :: Γ) := s.fv ∪ fv Γ

-- Domain of an environment
def dom : env V → finset V
  | []                 := ∅
  | (binding v _ :: Γ) := insert v (dom Γ)

-- Domain of an environment
@[inline, reducible]
def map (f : sch V → sch V) : env V → env V :=
  list.map (prod.map id f)

-- A variable is not bound in the environment
@[inline, reducible]
def unbound (x : V) (Γ : env V) : Prop :=
  x ∉ dom Γ

-- If every variable is bound only once in the environment
inductive uniq : env V → Prop
  | empty : uniq []
  | push  : Π (x : V) (s : sch V) (Γ : env V), Γ.unbound x → uniq Γ → uniq (Γ.add x s)

-- When the domains of two environments are disjoint
def disjoint (Γ₁ : env V) (Γ₂ : env V) : Prop :=
  dom Γ₁ ∩ dom Γ₂ = ∅

-- Get the first type scheme bound to the variable x
def get (x : V) : env V → option (sch V)
  | []                 := none
  | (binding y s :: t) := if h : y = x then some s else get t

end /- namespace -/ env --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
