/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sean Leather

Generating fresh atoms.

An atom (or inhabitant) of type `α` that is not a member of a given finite set
`s : finset α` is called “fresh.”

The set `s` is called the “avoidance set” since it contains the atoms to be
avoided when generating the fresh atom.

The `fresh` structure specifies a fresh atom generator given an avoidance
set.

The type `α` is countably infinite since a fresh atom must not be a member of
any given finite set.
-/
import data.finset

variables {α : Type*}

/-- Atom generator with proof that the generated atom is fresh for any
avoidance set. -/
structure fresh (α : Type*) :=
(gen : finset α → α)
(gen_not_mem : ∀ (s : finset α), gen s ∉ s)

namespace fresh

section decidable_eq_α
variables [decidable_eq α]

/- gen -/

theorem gen_ne_of_mem (F : fresh α) {a} {s : finset α} (h : a ∈ s) : a ≠ F.gen s :=
λ h', absurd (h' ▸ h : F.gen s ∈ s) (F.gen_not_mem s)

@[simp] theorem gen_not_mem_of_subset (F : fresh α) {s s' : finset α} (h : s ⊆ s') :
  F.gen s' ∉ s :=
λ h', absurd (finset.subset_iff.mp h h') (F.gen_not_mem s')

theorem gen_not_mem_singleton (F : fresh α) (a : α) :
  F.gen (finset.singleton a) ≠ a :=
finset.not_mem_singleton.mp $ F.gen_not_mem _

theorem gen_not_mem_insert (F : fresh α) (a : α) (s : finset α) :
  F.gen (insert a s) ≠ a ∧ F.gen (insert a s) ∉ s :=
not_or_distrib.mp $ mt finset.mem_insert.mpr $ F.gen_not_mem _

theorem gen_not_mem_union (F : fresh α) (s₁ s₂ : finset α) :
  F.gen (s₁ ∪ s₂) ∉ s₁ ∧ F.gen (s₁ ∪ s₂) ∉ s₂ :=
finset.not_mem_union.mp $ F.gen_not_mem _

theorem gen_ssubset_insert (F : fresh α) (s : finset α) : s ⊂ insert (F.gen s) s :=
finset.ssubset_insert (F.gen_not_mem s)

@[simp] theorem gen_insert_ne (F : fresh α) (s : finset α) :
  F.gen (insert (F.gen s) s) ≠ F.gen s :=
have h₁ : F.gen (insert (F.gen s) s) ∉ insert (F.gen s) s :=
  F.gen_not_mem (insert (F.gen s) s),
have F.gen s ∈ insert (F.gen s) s :=
  finset.mem_insert_self _ _,
λ h₂, by rw h₂ at h₁; contradiction

/- pgen -/

/-- Generate a pair of a fresh atom and a new avoidance set. -/
def pgen (F : fresh α) (s : finset α) : α × finset α :=
let a := F.gen s in ⟨a, insert a s⟩

theorem pgen_not_mem (F : fresh α) :
  ∀ (s : finset α), (F.pgen s).1 ∉ s :=
F.gen_not_mem

theorem pgen_subset (F : fresh α) (s : finset α) : s ⊆ (F.pgen s).2 :=
finset.subset_insert _ _

theorem pgen_ne_of_mem {a} (F : fresh α) (s : finset α) (h : a ∈ s) : a ≠ (F.pgen s).1 :=
F.gen_ne_of_mem h

/- pgenl -/

/-- Generate a pair of a fresh atom list of the given length and a new
avoidance set. -/
def pgenl (F : fresh α) (s : finset α) : ℕ → list α × finset α
| 0     := ⟨[], s⟩
| (n+1) :=
  have ih : list α × finset α := pgenl n,
  have a : α := F.gen ih.2,
  ⟨a :: ih.1, insert a ih.2⟩

@[simp] theorem pgenl_zero (F : fresh α) (s : finset α) :
  F.pgenl s 0 = prod.mk [] s :=
rfl

@[simp] theorem pgenl_succ (F : fresh α) (s : finset α) (n : ℕ) :
  F.pgenl s (n+1) =
  prod.mk (F.gen (F.pgenl s n).2 :: (F.pgenl s n).1)
          (insert (F.gen (F.pgenl s n).2) (F.pgenl s n).2) :=
by simp [pgenl]

theorem pgenl_length (F : fresh α) (s : finset α) :
  ∀ n, (F.pgenl s n).1.length = n
| 0     := rfl
| (n+1) := by simp *

theorem pgenl_subset (F : fresh α) (s : finset α) :
  ∀ n, s ⊆ (F.pgenl s n).2
| 0     := by simp
| (n+1) :=
  begin
    rcases finset.ssubset_iff.mp (F.gen_ssubset_insert (F.pgenl s n).2) with ⟨a, _, h₃⟩,
    have h₁ : s ⊆ (F.pgenl s n).2 := pgenl_subset _,
    have h₂ : (F.pgenl s n).2 ⊆ insert a (F.pgenl s n).2 := finset.subset_insert _ _,
    exact finset.subset.trans h₁ (finset.subset.trans h₂ h₃)
  end

theorem pgenl_list_subset (F : fresh α) (s : finset α) :
  ∀ n, ∀ a ∈ (F.pgenl s n).1, a ∈ (F.pgenl s n).2
| 0     := by simp
| (n+1) := λ a h, by simp at h; cases h; [simp [h], simp [pgenl_list_subset _ _ h]]

@[simp] theorem gen_pgenl_not_mem (F : fresh α) (s : finset α) (n : ℕ) :
  F.gen (F.pgenl s n).2 ∉ s :=
mt (λ p, finset.subset_iff.mp (F.pgenl_subset s n) p) (F.gen_not_mem _)

@[simp] theorem gen_pgenl_not_mem_list (F : fresh α) (s : finset α) (n : ℕ) :
  F.gen (F.pgenl s n).2 ∉ (F.pgenl s n).1 :=
mt (F.pgenl_list_subset s n _) (F.gen_not_mem (F.pgenl s n).2)

theorem pgenl_not_mem (F : fresh α) {s : finset α} {a} :
  ∀ {n}, a ∈ (F.pgenl s n).1 → a ∉ s
| 0     h := by cases h
| (n+1) h := by simp at h; cases h; [simp [h], simp [pgenl_not_mem h]]

theorem pgenl_nodup (F : fresh α) (s : finset α) :
  ∀ n, (F.pgenl s n).1.nodup
| 0     := list.nodup_nil
| (n+1) := list.nodup_cons_of_nodup (by simp) (pgenl_nodup n)

@[simp] theorem gen_pgenl_ne_of_mem (F : fresh α) {s : finset α} {a n} (h : a ∈ s) :
  a ≠ F.gen (F.pgenl s n).2 :=
F.gen_ne_of_mem $ finset.subset_iff.mp (F.pgenl_subset s n) h

theorem pgenl_not_mem_singleton_self (F : fresh α) (a) (n) :
  a ∉ (F.pgenl (finset.singleton a) n).1 :=
by induction n; simp *

theorem pgenl_mem_singleton (F : fresh α) {a b n}
  (h : a ∈ (F.pgenl (finset.singleton b) n).1) : a ≠ b :=
λ h', absurd (by simpa [h'] using h) (F.pgenl_not_mem_singleton_self b n)

theorem pgenl_mem_union (F : fresh α) {s₁ s₂ : finset α} {n a}
  (h : a ∈ (F.pgenl (s₁ ∪ s₂) n).1) : a ∉ s₁ ∧ a ∉ s₂ :=
finset.not_mem_union.mp $ F.pgenl_not_mem h

/- pgenf -/

/-- Generate a pair of a fresh atom set of the given cardinality and a new
avoidance set. -/
def pgenf (F : fresh α) (s : finset α) (n : ℕ) : finset α × finset α :=
⟨⟨(F.pgenl s n).1, F.pgenl_nodup s n⟩, (F.pgenl s n).2⟩

@[simp] theorem pgenf_zero (F : fresh α) (s : finset α) :
  F.pgenf s 0 = prod.mk ∅ s :=
rfl

@[simp] theorem pgenf_succ (F : fresh α) (s : finset α) (n : ℕ) :
  F.pgenf s (n+1) =
  prod.mk (insert (F.gen (F.pgenf s n).2) (F.pgenf s n).1)
          (insert (F.gen (F.pgenf s n).2) (F.pgenf s n).2) :=
by simp [pgenf]; congr; exact (list.insert_of_not_mem (F.gen_pgenl_not_mem_list s n)).symm

theorem pgenf_subset (F : fresh α) (s : finset α) (n : ℕ) :
  ∀ a ∈ (F.pgenf s n).1, a ∈ (F.pgenf s n).2 :=
F.pgenl_list_subset s n

theorem pgenf_not_mem (F : fresh α) (s : finset α) (n : ℕ) :
  F.gen (F.pgenf s n).2 ∉ (F.pgenf s n).1 :=
F.gen_pgenl_not_mem_list s n

end decidable_eq_α

end fresh

/- infinite nat -/

namespace finset

/-- Successor of the maximum: the minimum nat not a member of a finite set -/
def max_succ (s : finset ℕ) : ℕ :=
match s.max with
| none   := 0
| some m := m + 1
end

@[simp] theorem max_succ_empty : max_succ ∅ = 0 :=
rfl

@[simp] theorem max_succ_of_ne_empty {s : finset ℕ} (h : s ≠ ∅) :
  s.max_succ = s.max.iget + 1 :=
let ⟨m, hm⟩ := finset.max_of_ne_empty h in
by simp [option.mem_def.mp hm, max_succ, option.iget]

theorem max_succ_not_mem (s : finset ℕ) : s.max_succ ∉ s :=
λ h, if p : s = ∅ then
  by simpa [p] using h
else
  let ⟨m, hm⟩ := finset.max_of_ne_empty p in
  have hms : m+1 ∈ s := by simpa [max_succ, option.mem_def.mp hm] using h,
  m.not_succ_le_self $ le_max_of_mem hms hm

end finset

/-- A simple fresh nat generator -/
protected def fresh.nat : fresh ℕ :=
⟨finset.max_succ, finset.max_succ_not_mem⟩

/-- Tagged pair: a value and a natural number. This is useful for associating
strings with numbers and printing uniquely tagged strings. -/
@[derive decidable_eq]
structure tagged (α : Type*) :=
(val : α)
(tag : ℕ)

namespace tagged

instance [has_repr α] : has_repr (tagged α) :=
⟨λ ⟨a, t⟩, repr a ++ "_" ++ repr t⟩

def zero (a : α) : tagged α :=
⟨a, 0⟩

def succ : tagged α → tagged α
| ⟨a, t⟩ := ⟨a, t.succ⟩

variables [_root_.decidable_eq α]

/-- All tags for a given value. -/
def tags (s : finset (tagged α)) (a : α) : finset ℕ :=
(s.filter (λ (b : tagged α), a = b.val)).image tag

def fresh (a : α) (s : finset (tagged α)) : tagged α :=
mk a (tags s a).max_succ

theorem max_succ_tags_not_mem (a : α) (s : finset (tagged α)) : fresh a s ∉ s :=
have p : (tags s a).max_succ ∉ tags s a := finset.max_succ_not_mem _,
by simp [tags] at p; exact λ h, p _ h rfl rfl

end tagged

/-- A fresh tagged pair generator for a particular value. -/
protected def fresh.tagged [decidable_eq α] (a : α) : fresh (tagged α) :=
⟨λ s, tagged.fresh a s, λ s, tagged.max_succ_tags_not_mem a s⟩
