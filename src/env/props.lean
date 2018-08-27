/-

import .conv

namespace tts ------------------------------------------------------------------
namespace env ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {x x₁ x₂ y : V} -- Variable names
variables {t : typ V} -- Types
variables {s s₁ s₂ : sch V} -- Type schemes
variables {fs : sch V → sch V} -- Type scheme function
variables {b b₁ b₂ : binding V} -- Bindings
variables {Γ Γ₁ Γ₂ Γ₃ : env V} -- Environments

-- Use notation to avoid ambiguity.
local notation `∅` := has_emptyc.emptyc (env V)
local notation `singleton` := @singleton (binding V) (env V) _ _

local attribute [simp] conv.binding conv.empty conv.insert conv.one conv.append
local attribute [simp] conv.mem conv.map conv.fv conv.dom conv.disjoint conv.uniq
local attribute [simp] decidable.not_or_iff_and_not

section append -----------------------------------------------------------------

@[simp]
theorem append_empty_left : ∅ ++ Γ = Γ :=
  by cases Γ; simp

@[simp]
theorem append_empty_right : Γ ++ ∅ = Γ :=
  by cases Γ; simp

@[simp]
theorem append_insert : insert b Γ₁ ++ Γ₂ = insert b (Γ₁ ++ Γ₂) :=
  by cases Γ₁; cases Γ₂; simp

@[simp]
theorem append_assoc : Γ₁ ++ Γ₂ ++ Γ₃ = Γ₁ ++ (Γ₂ ++ Γ₃) :=
  by cases Γ₁; cases Γ₂; cases Γ₃; simp

end /- section -/ append -------------------------------------------------------

section mem --------------------------------------------------------------------

@[simp]
theorem mem_empty : b ∈ ∅ ↔ false :=
  by simp

@[simp]
theorem mem_insert : b₁ ∈ insert b₂ Γ ↔ (b₁ = b₂ ∨ b₁ ∈ Γ) :=
  by cases Γ; simp

@[simp]
theorem mem_one : b₁ ∈ one b₂ ↔ b₁ = b₂ :=
  by simp

@[simp]
theorem mem_append : b ∈ Γ₁ ++ Γ₂ ↔ b ∈ Γ₁ ∨ b ∈ Γ₂ :=
  by cases Γ₁; cases Γ₂; simp

theorem mem_append_weaken : b ∈ Γ₁ ++ Γ₃ → b ∈ Γ₁ ++ (Γ₂ ++ Γ₃) :=
  by simp; exact or.imp id or.inr

theorem mem_remove_mid_of_ne_var
: x₁ ≠ x₂
→ x₁ :~ s₁ ∈ Γ₁ ++ (one (x₂ :~ s₂) ++ Γ₂)
→ x₁ :~ s₁ ∈ Γ₁ ++ Γ₂ :=
  by cases Γ₁; cases Γ₂; exact binding_list.mem_remove_mid_of_ne_var

end /- section -/ mem ----------------------------------------------------------

section map --------------------------------------------------------------------

@[simp]
theorem map_empty : map fs ∅ = ∅ :=
  by simp

@[simp]
theorem map_insert : map fs (insert b Γ) = insert (b.var :~ fs b.sch) (map fs Γ) :=
  by cases Γ; simp

@[simp]
theorem map_one : map fs (one b) = one (b.var :~ fs b.sch) :=
  by simp

@[simp]
theorem map_append : map fs (Γ₁ ++ Γ₂) = map fs Γ₁ ++ map fs Γ₂ :=
  by cases Γ₁; cases Γ₂; simp

end /- section -/ map ----------------------------------------------------------

section fv ---------------------------------------------------------------------
variables [decidable_eq V]

theorem not_mem_sch_fv_of_not_mem_fv : x ∉ fv Γ → b ∈ Γ → x ∉ sch.fv b.sch :=
  by cases Γ; exact binding_list.not_mem_sch_fv_of_not_mem_fv

end /- section -/ fv -----------------------------------------------------------

section dom --------------------------------------------------------------------
variables [decidable_eq V]

@[simp]
theorem dom_empty : dom ∅ = finset.empty :=
  rfl

@[simp]
theorem dom_insert : dom (insert b Γ) = insert b.var (dom Γ) :=
  by cases Γ; simp

@[simp]
theorem dom_one : dom (one b) = finset.singleton b.var :=
  by simp; refl

@[simp]
theorem dom_append : dom (Γ₁ ++ Γ₂) = dom Γ₁ ∪ dom Γ₂ :=
  by cases Γ₁; cases Γ₂; simp

@[simp]
theorem dom_map : dom (map fs Γ) = dom Γ :=
  by cases Γ; simp

end /- section -/ dom ----------------------------------------------------------

section mem_dom ----------------------------------------------------------------
variables [decidable_eq V]

@[simp]
theorem mem_dom_empty : x ∈ dom ∅ ↔ false :=
  by refl

@[simp]
theorem mem_dom_insert : x₁ ∈ insert x₂ (dom Γ) ↔ x₁ = x₂ ∨ x₁ ∈ dom Γ :=
  by cases Γ; simp

@[simp]
theorem not_mem_dom_insert : x₁ ∉ insert x₂ (dom Γ) ↔ x₁ ≠ x₂ ∧ x₁ ∉ dom Γ :=
  by simp

@[simp]
theorem mem_dom_one : x ∈ dom (one b) ↔ x = b.var :=
  by simp

@[simp]
theorem not_mem_dom_one : x ∉ dom (one b) ↔ x ≠ b.var :=
  by simp

theorem ne_of_mem_dom_of_not_mem_dom : x₁ ∈ dom Γ → x₂ ∉ dom Γ → x₁ ≠ x₂ :=
  ne_of_mem_of_not_mem

theorem ne_of_not_mem_dom_one : x₁ ∉ dom (one (x₂ :~ s)) → x₁ ≠ x₂ :=
  by simp

theorem ne_of_not_mem_dom_mid : x₁ ∉ dom (Γ₁ ++ (one (x₂ :~ s) ++ Γ₂)) → x₁ ≠ x₂ :=
  by cases Γ₁; cases Γ₂; simp; exact λ p _ _, p

theorem mem_dom_of_mem : b ∈ Γ → b.var ∈ dom Γ :=
  by cases Γ; cases b; exact binding_list.mem_dom_of_mem

end /- section -/ mem_dom ------------------------------------------------------

section disjoint ---------------------------------------------------------------
variables [decidable_eq V]

theorem disjoint_forall : disjoint Γ₁ Γ₂ ↔ ∀ {b : binding V}, b ∈ Γ₁ → b.var ∉ dom Γ₂ :=
  by cases Γ₁; cases Γ₂; exact binding_list.disjoint_forall

theorem disjoint.symm : disjoint Γ₁ Γ₂ → disjoint Γ₂ Γ₁ :=
  by cases Γ₁; cases Γ₂; exact disjoint.symm

theorem disjoint_comm (Γ₁ Γ₂ : env V) : disjoint Γ₁ Γ₂ ↔ disjoint Γ₂ Γ₁ :=
  by cases Γ₁; cases Γ₂; exact disjoint.comm

@[simp]
theorem disjoint_nil : disjoint ∅ Γ ↔ true :=
  by cases Γ; simp

@[simp]
theorem disjoint_insert_left : disjoint (insert b Γ₁) Γ₂ ↔ b.var ∉ dom Γ₂ ∧ disjoint Γ₁ Γ₂ :=
  by cases Γ₁; cases Γ₂; simp

@[simp]
theorem disjoint_insert_right : disjoint Γ₁ (insert b Γ₂) ↔ b.var ∉ dom Γ₁ ∧ disjoint Γ₁ Γ₂ :=
  by cases Γ₁; cases Γ₂; simp

@[simp]
theorem disjoint_one_left : disjoint (one b) Γ ↔ b.var ∉ dom Γ :=
  by cases Γ; simp

@[simp]
theorem disjoint_one_right : disjoint Γ (one b) ↔ b.var ∉ dom Γ :=
  by rw [disjoint_comm _ _, disjoint_one_left]

@[simp]
theorem disjoint_append_left : disjoint (Γ₁ ++ Γ₂) Γ₃ ↔ disjoint Γ₁ Γ₃ ∧ disjoint Γ₂ Γ₃ :=
  by cases Γ₁; cases Γ₂; cases Γ₃; simp

@[simp]
theorem disjoint_append_right : disjoint Γ₁ (Γ₂ ++ Γ₃) ↔ disjoint Γ₁ Γ₂ ∧ disjoint Γ₁ Γ₃ :=
  by cases Γ₁; cases Γ₂; cases Γ₃; simp

@[simp]
theorem disjoint_map_left : disjoint (map fs Γ₁) Γ₂ ↔ disjoint Γ₁ Γ₂ :=
  by cases Γ₁; cases Γ₂; simp

@[simp]
theorem disjoint_map_right : disjoint Γ₁ (map fs Γ₂) ↔ disjoint Γ₁ Γ₂ :=
  by rw [disjoint_comm Γ₁ _, disjoint_map_left, disjoint_comm Γ₂ _]

end /- section -/ disjoint -----------------------------------------------------

section uniq -------------------------------------------------------------------
variables [decidable_eq V]

@[simp]
theorem uniq_empty : uniq ∅ ↔ true :=
  by simp

@[simp]
theorem uniq_insert : uniq (insert b Γ) ↔ b.var ∉ dom Γ ∧ uniq Γ :=
  by cases Γ; cases b; simp

@[simp]
theorem uniq_one : uniq (one b) ↔ true :=
  by simp

@[simp]
theorem uniq_append : uniq (Γ₁ ++ Γ₂) ↔ uniq Γ₁ ∧ uniq Γ₂ ∧ disjoint Γ₁ Γ₂ :=
  by cases Γ₁; cases Γ₂; simp

@[simp]
theorem uniq_remove_mid : uniq (Γ₁ ++ (Γ₂ ++ Γ₃)) → uniq (Γ₁ ++ Γ₃) :=
  by cases Γ₁; cases Γ₂; cases Γ₃; exact binding_list.uniq_remove_mid

@[simp]
theorem uniq_map : uniq (map fs Γ) ↔ uniq Γ :=
  by cases Γ; simp

end /- section -/ uniq ---------------------------------------------------------

section mem_map ----------------------------------------------------------------
open function 

theorem mem_map_of_inj : injective fs → (x :~ fs s ∈ map fs Γ ↔ x :~ s ∈ Γ) :=
  λ h, by cases Γ; exact binding_list.mem_map_of_inj h

theorem mem_map : x :~ s₁ ∈ map fs Γ ↔ ∃ s₂, x :~ s₂ ∈ Γ ∧ fs s₂ = s₁ :=
  by cases Γ; exact binding_list.mem_map

theorem mem_map_of_mem : x :~ s ∈ Γ → x :~ fs s ∈ map fs Γ :=
  by cases Γ; exact binding_list.mem_map_of_mem

end /- section -/ mem_map ------------------------------------------------------

section uniq -------------------------------------------------------------------
variables [decidable_eq V]

theorem mem_insert_of_uniq_insert
: uniq (insert (x₂ :~ s₂) Γ)
→ (x₁ :~ s₁ ∈ insert (x₂ :~ s₂) Γ ↔ x₁ = x₂ ∧ s₁ = s₂ ∧ x₁ ∉ dom Γ ∨ x₁ :~ s₁ ∈ Γ ∧ x₁ ≠ x₂) :=
  by cases Γ; exact binding_list.mem_cons_of_uniq_cons

theorem mem_append_of_uniq_append
: uniq (Γ₁ ++ Γ₂)
→ (x :~ s ∈ Γ₁ ++ Γ₂ ↔ x :~ s ∈ Γ₁ ∧ x ∉ dom Γ₂ ∨ x ∉ dom Γ₁ ∧ x :~ s ∈ Γ₂) :=
  by cases Γ₁; cases Γ₂; exact binding_list.mem_append_of_uniq_append

theorem eq_sch_of_uniq_one_mid_of_mem_one_mid
: uniq (Γ₁ ++ (one (x :~ s₂) ++ Γ₂))
→ x :~ s₁ ∈ Γ₁ ++ (one (x :~ s₂) ++ Γ₂)
→ s₁ = s₂ :=
  by cases Γ₁; cases Γ₂; exact binding_list.eq_sch_of_uniq_one_mid_of_mem_one_mid

end /- section -/ uniq ---------------------------------------------------------

section sch_subst --------------------------------------------------------------
variables [decidable_eq V]

theorem sch_subst_mem_of_not_mem_sch_fv (h : x ∉ sch.fv s)
: y :~ s ∈ Γ → y :~ sch.subst x t s ∈ Γ :=
  by simp [sch.subst_fresh h]

theorem sch_subst_mem_of_not_mem_fv (h₁ : x ∉ fv Γ) (h₂ : y :~ s ∈ Γ)
: y :~ sch.subst x t s ∈ Γ :=
  sch_subst_mem_of_not_mem_sch_fv (not_mem_sch_fv_of_not_mem_fv h₁ h₂) h₂

theorem sch_subst_mem (h : y :~ s ∈ Γ)
: y :~ sch.subst x t s ∈ map (sch.subst x t) Γ :=
  by cases Γ; exact binding_list.sch_subst_mem h

end /- section -/ sch_subst ----------------------------------------------------

end /- namespace -/ env --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------

-/
