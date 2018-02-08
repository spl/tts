import .sch
import data.finset

namespace tts ------------------------------------------------------------------

def env (V : Type) : Type :=
  list (V × sch V)

variables {V : Type} [decidable_eq V] -- Type of variable names

namespace env ------------------------------------------------------------------

instance : has_emptyc (env V) :=
  ⟨list.nil⟩

instance : has_append (env V) :=
  ⟨list.append⟩

instance : has_mem (V × sch V) (env V) :=
  ⟨list.mem⟩

def one (x : V) (s : sch V) : env V :=
  [⟨x, s⟩]

def add (x : V) (s : sch V) (Γ : env V) : env V :=
   one x s ++ Γ

-- Get the free variables of an environment.
def fv (Γ : env V) : finset V :=
  list.foldr (λ (p : V × sch V) (vs : finset V), p.snd.fv ∪ vs) ∅ Γ

def dom [decidable_eq V] (Γ : env V) : finset V :=
  list.to_finset (list.map prod.fst Γ)

def unbound [decidable_eq V] (x : V) (Γ : env V) : Prop :=
  x ∉ dom Γ

-- A predicate that holds if every variable is bound only once in the
-- environment.
inductive uniq : env V → Prop
  | empty : uniq []
  | push  : Π [decidable_eq V] (x : V) (s : sch V) (Γ : env V), Γ.unbound x → uniq Γ → uniq (Γ.add x s)

def get [decidable_eq V] (x : V) : env V → option (sch V)
  | []            := none
  | (⟨y, s⟩ :: Γ) := if x = y then some s else get Γ

def binds (x : V) (s : sch V) (Γ : env V) : Prop :=
  prod.mk x s ∈ Γ

def maps [decidable_eq V] (x : V) (s : sch V) (Γ : env V) : Prop :=
  get x Γ = some s

end /- namespace -/ env --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
