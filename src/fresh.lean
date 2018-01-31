import data.finset

namespace tts ------------------------------------------------------------------
variables {V : Type} [has_insert V (finset V)] -- Type of variable names

def fresh : finset V → ℕ → list V → Prop
  | vs 0     []        := true
  | vs (n+1) (x :: xs) := x ∉ vs ∧ fresh (insert x vs) n xs
  | _  _     _         := false

end /- namespace -/ tts --------------------------------------------------------
