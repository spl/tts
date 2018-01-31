import .typ
import data.finset

namespace tts ------------------------------------------------------------------
variables {V : Type} -- Type of variable names

def env (V : Type) : Type :=
  list (V × sch V)

namespace env ------------------------------------------------------------------

instance : has_emptyc (env V) :=
  ⟨list.nil⟩

def singleton (x : V) (s : sch V) : env V :=
  [⟨x, s⟩]

instance : has_append (env V) :=
  ⟨list.append⟩

def add (x : V) (s : sch V) (Γ : env V) : env V :=
  Γ ++ singleton x s

def dom [decidable_eq V] (Γ : env V) : finset V :=
  list.to_finset (list.map prod.fst Γ)

def unbound [decidable_eq V] (x : V) (Γ : env V) : Prop :=
  x ∉ dom Γ

inductive ok : env V → Prop
  | empty : ok ∅
  | push  : Π [decidable_eq V] (Γ : env V) (x : V) (s : sch V), ok Γ → Γ.unbound x → ok (Γ.add x s)

def get [decidable_eq V] (x : V) : env V → option (sch V)
  | []            := none
  | (⟨y, s⟩ :: Γ) := if x = y then some s else get Γ

def binds [decidable_eq V] (x : V) (s : sch V) (Γ : env V) : Prop :=
  get x Γ = some s

end /- namespace -/ env --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
