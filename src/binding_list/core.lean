-- These are definitions on the underlying list of bindings.

import .binding

namespace tts ------------------------------------------------------------------
namespace binding_list ---------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names

-- Free variables of a binding list
def fv : list (binding V) → finset V
  | []       := ∅
  | (b :: Γ) := sch.fv b.sch ∪ fv Γ

-- Domain of a binding list
def dom : list (binding V) → finset V
  | []       := ∅
  | (b :: Γ) := insert b.var (dom Γ)

-- When the domains of two binding lists are disjoint
def disjoint (Γ₁ : list (binding V)) (Γ₂ : list (binding V)) : Prop :=
  disjoint (dom Γ₁) (dom Γ₂)

-- If every variable is bound only once in the binding list
inductive uniq : list (binding V) → Prop
  | nil  :                                                                    uniq []
  | cons : Π {b : binding V} {Γ : list (binding V)}, b.var ∉ dom Γ → uniq Γ → uniq (b :: Γ)

end /- namespace -/ binding_list -----------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
