import data.finset.disjoint_list

namespace finset ---------------------------------------------------------------
universes u
variables {α : Type u} {β : Type u → Type u}

-- This type class specifies a function for producing “fresh” elements not
-- found in a finite set. It is one way to say that the element type is infinite.

class has_fresh (α : Type*) :=
  -- Produce a fresh element from a finite set.
  (fresh : finset α → α)
  -- A fresh element of a finite set is not a member of that set.
  (fresh_not_mem : ∀ (s : finset α), fresh s ∉ s)

variables [has_fresh α]

def fresh : finset α → α:=
  has_fresh.fresh

def fresh_not_mem : ∀ (s : finset α), fresh s ∉ s :=
  has_fresh.fresh_not_mem

section decidable_eq -----------------------------------------------------------
variables [decidable_eq α]

def fresh_build (ε : β α) (ι : α → β α → β α) (ϕ : β α → finset α) (s : finset α) : ℕ → β α
  | 0     := ε
  | (n+1) := let f' := fresh_build n in ι (fresh (ϕ f' ∪ s)) f'

-- Given a finite set of elements and a cardinality, produce a finite set of
-- fresh elements with the given cardinality.

@[inline, reducible]
def fresh_finset : finset α → ℕ → finset α :=
  fresh_build ∅ insert id

-- Given a finite set of elements and a length, produce a list of fresh
-- elements with the given length.

@[inline, reducible]
def fresh_list : finset α → ℕ → list α :=
  fresh_build [] list.cons list.to_finset

end /- section -/ decidable_eq -------------------------------------------------

section decidable_eq -----------------------------------------------------------
variables [decidable_eq α]

@[simp]
theorem fresh_finset_zero (s : finset α) : fresh_finset s 0 = ∅ :=
  rfl

@[simp]
theorem fresh_finset_succ (s : finset α) (n : ℕ)
: fresh_finset s (nat.succ n) = insert (fresh (fresh_finset s n ∪ s)) (fresh_finset s n) :=
  rfl

def fresh_finset_card (s : finset α) : ∀ n, card (fresh_finset s n) = n
  | 0     := rfl
  | (n+1) :=
    let ⟨p, _⟩ := not_mem_union.mp (fresh_not_mem (fresh_finset s n ∪ s)) in
    by rw fresh_finset_succ;
       conv { to_rhs, rw ←fresh_finset_card n };
       exact card_insert_of_not_mem p

def fresh_finset_disjoint (s : finset α) : ∀ n, fresh_finset s n ∩ s = ∅
  | 0     := rfl
  | (n+1) :=
    let ⟨_, p⟩ := not_mem_union.mp (fresh_not_mem (fresh_finset s n ∪ s)) in
    by rw [fresh_finset_succ, insert_inter_of_not_mem p, fresh_finset_disjoint n]

@[simp]
theorem fresh_list_zero (s : finset α) : fresh_list s 0 = [] :=
  rfl

@[simp]
theorem fresh_list_succ (s : finset α) (n : ℕ)
: fresh_list s (n + 1) = fresh ((fresh_list s n).to_finset ∪ s) :: fresh_list s n :=
  rfl

theorem fresh_list_length (s : finset α) : ∀ n, (fresh_list s n).length = n
  | 0     := rfl
  | (n+1) := by simp [fresh_list_length n]

theorem fresh_list_nodup (s : finset α) : ∀ n, (fresh_list s n).nodup
  | 0     := list.nodup_nil
  | (n+1) :=
    let ⟨p, _⟩ := not_mem_union.mp (fresh_not_mem ((fresh_list s n).to_finset ∪ s)) in
    list.nodup_cons_of_nodup ((not_iff_not_of_iff list.mem_to_finset).mp p) (fresh_list_nodup n)

theorem fresh_list_disjoint (s : finset α) : ∀ n, disjoint_list (fresh_list s n) s
  | 0     := rfl
  | (n+1) :=
    let ⟨_, p⟩ := not_mem_union.mp (fresh_not_mem ((fresh_list s n).to_finset ∪ s)) in
    by rw [fresh_list_succ, disjoint_list_cons]; exact ⟨p, fresh_list_disjoint n⟩

theorem fresh_list_disjoint_union {s₁ s₂ : finset α} {n}
: disjoint_list (fresh_list (s₁ ∪ s₂) n) (s₁ ∪ s₂)
↔ disjoint_list (fresh_list (s₁ ∪ s₂) n) s₁ ∧ disjoint_list (fresh_list (s₁ ∪ s₂) n) s₂ :=
  by induction n; simp

end /- section -/ decidable_eq -------------------------------------------------

end /- namespace -/ finset -----------------------------------------------------

namespace nat ------------------------------------------------------------------

@[simp]
theorem max_zero_right (a : ℕ) : max a 0 = a :=
  by by_cases h : a ≤ 0; simp [max, h]; exact (eq_zero_of_le_zero h).symm

@[simp]
theorem max_zero_left (a : ℕ) : max 0 a = a :=
  max_comm a 0 ▸ max_zero_right a

end /- namespace -/ nat --------------------------------------------------------

namespace finset ---------------------------------------------------------------

def max_nat : finset ℕ → ℕ :=
  fold max 0 id

theorem max_nat_singleton (a : ℕ) : max_nat {a} = a :=
  nat.max_zero_right a

theorem max_nat_insert {a : ℕ} {s : finset ℕ} (p : a ∉ s)
: max_nat (insert a s) = max a (max_nat s) :=
  fold_insert p

def max_nat_le {a : ℕ} {s : finset ℕ} : a ∈ s → a ≤ max_nat s :=
  finset.induction
    (λ (h : a ∈ ∅), false.elim (@not_mem_empty _ a h))
    (λ b s (h : b ∉ s) ih a_in_insert_b_s,
      begin
        by_cases p : s = ∅,
        begin
          subst p,
          have : max_nat (insert b ∅) = b, from max_nat_singleton b,
          rw [this, mem_singleton.mp a_in_insert_b_s]
        end,
        begin
          rw max_nat_insert h,
          cases mem_insert.mp a_in_insert_b_s,
          case or.inl : h {
            induction h,
            exact le_max_left a (max_nat s)
          },
          case or.inr : h {
            exact le_trans (ih h) (le_max_right b (max_nat s))
          }
        end,
      end)
    s

instance has_fresh.nat : has_fresh ℕ :=
  ⟨ λ s, nat.succ (max_nat s)
  , λ s (h : nat.succ (max_nat s) ∈ s),
    nat.not_succ_le_self (max_nat s) (max_nat_le h)
  ⟩

end /- namespace -/ finset -----------------------------------------------------
