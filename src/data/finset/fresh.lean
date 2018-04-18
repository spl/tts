import data.list.to_finset

namespace finset ---------------------------------------------------------------
variables {α : Type*}

class has_fresh (α : Type*) :=
  (fresh : ∀ (s : finset α), Σ' a, a ∉ s)

variables [has_fresh α]

-- Given finite set of elements, produce an element and a proof that the
-- element is not a member of the given set.

def fresh (s : finset α) : Σ' a, a ∉ s :=
  has_fresh.fresh s

variables [decidable_eq α]

-- Given a finite set of elements and a cardinality, produce a new finite set
-- of elements along with proofs that the set has the given cardinality and is
-- disjoint with the given set.

def fresh_finset (s₁ : finset α) : ∀ n, Σ' (s₂ : finset α), card s₂ = n ∧ s₂ ∩ s₁ = ∅
  | 0     := ⟨∅, rfl, rfl⟩
  | (n+1) :=
    match fresh_finset n with ⟨s₂, card_s₂_eq_n, s₂_disjoint_s₁⟩ :=
      have fr : Σ' a, a ∉ s₂ ∪ s₁ := fresh (s₂ ∪ s₁),
      have nm : fr.1 ∉ s₂ ∧ fr.1 ∉ s₁ := not_mem_union.mp fr.2,
      ⟨ insert fr.1 s₂
      , card_s₂_eq_n ▸ card_insert_of_not_mem nm.1
      , by rw insert_inter_of_not_mem nm.2; exact s₂_disjoint_s₁
      ⟩
    end

-- Given a finite set of elements and a length, produce a list of elements
-- along with proofs that the list has the given length, has no duplicates, and
-- is disjoint with the given set.

def fresh_list (s : finset α) : ∀ n, Σ' (l : list α), l.length = n ∧ l.nodup ∧ l.to_finset ∩ s = ∅
  | 0     := ⟨[], rfl, list.nodup_nil, rfl⟩
  | (n+1) :=
    match fresh_list n with ⟨l, l_length_eq_n, l_nodup, l_disjoint_s⟩ :=
      have f : Σ' a, a ∉ l.to_finset ∪ s := fresh (l.to_finset ∪ s),
      have nm : f.1 ∉ l.to_finset ∧ f.1 ∉ s := not_mem_union.mp f.2,
      ⟨ f.1 :: l
      , by simp [l_length_eq_n]
      , list.nodup_cons_of_nodup ((not_iff_not_of_iff list.mem_to_finset).mp nm.1) l_nodup
      , by rw [list.to_finset_cons, insert_inter_of_not_mem nm.2]; exact l_disjoint_s
      ⟩
    end

end /- namespace -/ finset -----------------------------------------------------
