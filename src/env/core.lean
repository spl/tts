import binding_list

namespace tts ------------------------------------------------------------------

-- An environment is list of variable-type scheme bindings.
structure env (V : Type) : Type :=
  (bindings : list (binding V))

variables {V : Type} -- Type of variable names

-- These are definitions on the environment. Some of them wrap the binding_list
-- definitions.
namespace env ------------------------------------------------------------------

-- An empty environment
instance : has_emptyc (env V) :=
  ⟨⟨list.nil⟩⟩

-- Add a binding to an environment
instance has_insert : has_insert (binding V) (env V) :=
  ⟨λ b ⟨Γ⟩, ⟨b :: Γ⟩⟩

-- A singleton environment
def one (b : binding V) : env V :=
  ⟨[b]⟩

-- A binding appears somewhere in the environment
instance has_mem : has_mem (binding V) (env V) :=
  ⟨λ b ⟨Γ⟩, b ∈ Γ⟩

-- Append one environment to another
instance has_append : has_append (env V) :=
  ⟨λ ⟨Γ₁⟩ ⟨Γ₂⟩, ⟨Γ₁ ++ Γ₂⟩⟩

-- Map a function over the type scheme of an environment
def map (f : sch V → sch V) : env V → env V
  | ⟨Γ⟩ := ⟨Γ.map (binding.map f)⟩

variables [decidable_eq V]

-- Free variables of an environment
def fv : env V → finset V
  | ⟨Γ⟩ := binding_list.fv Γ

-- Domain of an environment
def dom : env V → finset V
  | ⟨Γ⟩ := binding_list.dom Γ

-- When the domains of two environments are disjoint
def disjoint : env V → env V → Prop
  | ⟨Γ₁⟩ ⟨Γ₂⟩ := binding_list.disjoint Γ₁ Γ₂

-- If every variable is bound only once in the environment
def uniq : env V → Prop
  | ⟨Γ⟩ := binding_list.uniq Γ

end /- namespace -/ env --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
