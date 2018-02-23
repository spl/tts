import data.finset.extra

namespace tts ------------------------------------------------------------------
variables {V : Type} [decidable_eq V] -- Type of variable names
variables {L L₁ L₂ : finset V} -- Variable sets
variables {x : V} -- Variables
variables {xs : list V} -- Lists of variables

def fresh : list V → finset V → Prop
  | []        L := true
  | (x :: xs) L := x ∉ L ∧ fresh xs (insert x L)

@[simp]
theorem fresh_nil : fresh [] L ↔ true :=
  by rw fresh

@[simp]
theorem fresh_cons : fresh (x :: xs) L ↔ x ∉ L ∧ fresh xs (insert x L) :=
  by rw fresh

@[simp]
theorem fresh_union : fresh xs (L₁ ∪ L₂) ↔ fresh xs L₁ ∧ fresh xs L₂ :=
  begin
    induction xs with hd tl ih generalizing L₁ L₂; simp [decidable.not_or_iff_and_not, and.assoc],
    rw [finset.insert_union_distrib hd L₁ L₂, ih],
    simp [and.left_comm]
  end

end /- namespace -/ tts --------------------------------------------------------
