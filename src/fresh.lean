import data.finset.extra

namespace tts ------------------------------------------------------------------
variables {V : Type} [decidable_eq V] -- Type of variable names
variables {L L₁ L₂ : finset V} -- Variable sets
variables {x : V} -- Variables
variables {xs : list V} -- Lists of variables

-- Freshness of a list of variables from a set L and from one another
def fresh (L : finset V) : list V → Prop
  | []        := true
  | (x :: xs) := x ∉ xs ∧ x ∉ L ∧ fresh xs

@[simp]
theorem fresh_nil : fresh L [] ↔ true :=
  by rw fresh

@[simp]
theorem fresh_cons : fresh L (x :: xs) ↔ x ∉ xs ∧ x ∉ L ∧ fresh L xs :=
  by rw fresh

@[simp]
theorem fresh_union : fresh (L₁ ∪ L₂) xs ↔ fresh L₁ xs ∧ fresh L₂ xs :=
  begin
    induction xs with hd tl ih generalizing L₁ L₂; simp [decidable.not_or_iff_and_not, and.assoc, and.left_comm],
    rw ih,
    exact ⟨λ ⟨a, b, c, d, e⟩, ⟨a, b, c, c, d, e⟩, λ ⟨a, b, c, _, d, e⟩, ⟨a, b, c, d, e⟩⟩
  end

end /- namespace -/ tts --------------------------------------------------------
