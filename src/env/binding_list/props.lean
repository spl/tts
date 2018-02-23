import .defs
import logic.basic

open function

namespace tts ------------------------------------------------------------------
namespace binding_list ---------------------------------------------------------

variables {V : Type} -- Type of variable names
variables {x x₁ x₂ : V} -- Variables
variables {s s₁ s₂ : sch V} -- Type schemes
variables {fs : sch V → sch V} -- Type scheme function
variables {b : binding V} -- Bindings
variables {Γ Γ₁ Γ₂ Γ₃ : list (binding V)} -- Binding lists

-- Use notation to avoid ambiguity.
local notation `[]` := (list.nil : list (binding V))
local notation h :: t  := (list.cons h (t : list (binding V)) : list (binding V))

-- Keep and-chains right-associated
local attribute [simp] and.assoc

-- Conjunctive normal form
local attribute [simp] decidable.not_or_iff_and_not

@[inline, reducible, simp]
private
def map (fs : sch V → sch V) : list (binding V) → list (binding V) :=
  list.map (binding.map fs)

-- Basic properties of binding
section binding ----------------------------------------------------------------

@[simp]
theorem binding_var : (x :~ s).var = x :=
  rfl

@[simp]
theorem binding_sch : (x :~ s).sch = s :=
  rfl

@[simp]
theorem binding_map : binding.map fs (x :~ s) = x :~ fs s :=
  rfl

theorem binding_map_inj (fs_inj : injective fs) : injective (binding.map fs) :=
  λ ⟨x₁, s₁⟩ ⟨x₂, s₂⟩ h,
  begin
    injection h with h_x h_fs_s,
    have h_s : s₁ = s₂ := fs_inj h_fs_s,
    subst h_x,
    subst h_s
  end

end /- section -/ binding ------------------------------------------------------

-- Basic properties of mem and map
section mem_map ----------------------------------------------------------------

@[simp]
theorem map_cons : map fs (b :: Γ) = b.var :~ fs b.sch :: map fs Γ :=
  by cases b; refl

end /- section -/ mem_map ------------------------------------------------------

-- Basic properties of dom
section dom --------------------------------------------------------------------
variables [decidable_eq V]
local attribute [simp] dom

@[simp]
theorem dom_nil : dom [] = (∅ : finset V) :=
  rfl

@[simp]
theorem dom_one : dom [x :~ s] = finset.singleton x :=
  rfl

@[simp]
theorem dom_cons_val : (dom (x :~ s :: Γ)).val = multiset.ndinsert x ((dom Γ).val) :=
  begin
    cases Γ,
    case list.nil { simp },
    case list.cons : hd tl { cases hd, simp }
  end

@[simp]
theorem dom_cons_insert : dom (b :: Γ) = insert b.var (dom Γ) :=
  by cases b; simp

@[simp]
theorem dom_append : dom (Γ₁ ++ Γ₂) = dom Γ₁ ∪ dom Γ₂ :=
  by induction Γ₁ with _ _ ih; simp; simp [ih]

@[simp]
theorem dom_map : dom (map fs Γ) = dom Γ :=
  by induction Γ with _ _ ih; simp; simp [ih]

@[simp]
theorem mem_dom_wrap : x ∈ (dom Γ).val ↔ x ∈ dom Γ :=
  by induction Γ with hd tl ih; [simp, {cases hd, simp [ih]}]

@[simp]
theorem mem_dom_nil : x ∈ dom [] ↔ false :=
  by refl

@[simp]
theorem not_mem_dom_map : x ∉ dom (map fs Γ) ↔ x ∉ dom Γ :=
  by simp

end /- section -/ dom ----------------------------------------------------------

-- Basic properties of disjoint
section disjoint ---------------------------------------------------------------
variables [decidable_eq V]

theorem disjoint_multiset : disjoint Γ₁ Γ₂ ↔ multiset.disjoint (dom Γ₁).val (dom Γ₂).val :=
  finset.inter_eq_empty_iff_disjoint

-- We reuse the multiset simplifier theorems in this section.
local attribute [simp] disjoint_multiset

theorem disjoint.symm : disjoint Γ₁ Γ₂ → disjoint Γ₂ Γ₁ :=
  by simp

theorem disjoint_comm : disjoint Γ₁ Γ₂ ↔ disjoint Γ₂ Γ₁ :=
  by simp

@[simp]
theorem disjoint_nil : disjoint [] Γ ↔ true :=
  iff_true_intro (by simp)

@[simp]
theorem disjoint_one : disjoint [x :~ s] Γ ↔ x ∉ dom Γ :=
  by simp

private
lemma not_mem_dom_of_disjoint_cons : disjoint (b :: Γ₁) Γ₂ → b.var ∉ dom Γ₂ :=
  by intro h; simp at h; exact h.1

private
lemma disjoint_of_disjoint_cons : disjoint (b :: Γ₁) Γ₂ → disjoint Γ₁ Γ₂ :=
  by simp

private
lemma disjoint_cons : b.var ∉ dom Γ₂ → disjoint Γ₁ Γ₂ → disjoint (b :: Γ₁) Γ₂ :=
  by simp; exact and.intro

@[simp]
theorem disjoint_cons : disjoint (b :: Γ₁) Γ₂ ↔ b.var ∉ dom Γ₂ ∧ disjoint Γ₁ Γ₂ :=
  ⟨ λ h, ⟨not_mem_dom_of_disjoint_cons h, disjoint_of_disjoint_cons h⟩
  , λ h, disjoint_cons h.1 h.2
  ⟩

@[simp]
theorem disjoint_append : disjoint (Γ₁ ++ Γ₂) Γ₃ ↔ disjoint Γ₁ Γ₃ ∧ disjoint Γ₂ Γ₃ :=
  by simp

@[simp]
theorem disjoint_map : disjoint (map fs Γ₁) Γ₂ ↔ disjoint Γ₁ Γ₂ :=
  by simp

end /- section -/ disjoint -----------------------------------------------------

-- Basic properties of uniq
section uniq -------------------------------------------------------------------
variables [decidable_eq V]

@[simp]
theorem uniq_empty : uniq [] ↔ true :=
  iff_true_intro uniq.nil

@[simp]
theorem uniq_one : uniq [b] ↔ true :=
  iff_true_intro (uniq.cons mem_dom_nil.mp uniq.nil)

@[simp]
theorem uniq_cons : uniq (b :: Γ) ↔ b.var ∉ dom Γ ∧ uniq Γ :=
  ⟨λ u, by cases u with _ _ hd tl; exact ⟨hd, tl⟩, λ ⟨hd, tl⟩, uniq.cons hd tl⟩

private
lemma uniq_append_left : uniq (Γ₁ ++ Γ₂) → uniq Γ₁ ∧ uniq Γ₂ ∧ disjoint Γ₁ Γ₂ :=
  begin
    induction Γ₁ with hd tl ih; [simp, {cases hd, simp}],
    intros ub₁ ub₂ u,
    have p : uniq tl ∧ uniq Γ₂ ∧ disjoint tl Γ₂ := ih u,
    exact ⟨ub₂, ⟨p.1, ⟨p.2.1, ⟨ub₁, p.2.2⟩⟩⟩⟩
  end

private
lemma uniq_append_right : uniq Γ₁ ∧ uniq Γ₂ ∧ disjoint Γ₁ Γ₂ → uniq (Γ₁ ++ Γ₂) :=
  begin
    induction Γ₁ with hd tl ih; [simp, {cases hd, simp [ih]}],
    intros ub_tl un_tl un_Γ₂ ub_Γ₂ d_tl_Γ₂,
    exact ⟨ub_Γ₂, ⟨ub_tl, ih ⟨un_tl, un_Γ₂, d_tl_Γ₂⟩⟩⟩
  end

@[simp]
theorem uniq_append : uniq (Γ₁ ++ Γ₂) ↔ uniq Γ₁ ∧ uniq Γ₂ ∧ disjoint Γ₁ Γ₂ :=
  ⟨uniq_append_left, uniq_append_right⟩

@[simp]
theorem uniq_map : uniq (map fs Γ) ↔ uniq Γ :=
  by induction Γ with hd tl ih; [simp, {cases hd, simp [ih]}]

end /- section -/ uniq ---------------------------------------------------------

-- More properties of mem
section mem --------------------------------------------------------------------

private
lemma mem_map_of_inj' (h : injective (binding.map fs))
: binding.map fs (x :~ s) ∈ list.map (binding.map fs) Γ ↔ x :~ s ∈ Γ :=
  list.mem_map_of_inj h

theorem mem_map_of_inj (h : injective fs)
: x :~ fs s ∈ map fs Γ ↔ x :~ s ∈ Γ :=
  mem_map_of_inj' (binding_map_inj h)

theorem mem_map : x :~ s₁ ∈ map fs Γ ↔ ∃ s₂, x :~ s₂ ∈ Γ ∧ fs s₂ = s₁ :=
  begin
    split,
    begin
      intro h,
      rcases list.mem_map.mp h with ⟨b, h₁, h₂⟩,
      cases b with x₂ s₂,
      injection h₂ with h_x h_fs_s,
      subst h_x,
      exact ⟨s₂, ⟨h₁, h_fs_s⟩⟩
    end,
    begin
      intro h,
      rcases h with ⟨s₂, h₁, h₂⟩,
      exact list.mem_map.mpr ⟨x :~ s₂, ⟨h₁, by rw [binding.map, h₂]⟩⟩
    end
  end

private
lemma mem_map_of_mem'
: x :~ s ∈ Γ → binding.map fs (x :~ s) ∈ list.map (binding.map fs) Γ :=
  list.mem_map_of_mem (binding.map fs)

theorem mem_map_of_mem : x :~ s ∈ Γ → x :~ fs s ∈ map fs Γ :=
  mem_map_of_mem'

variables [decidable_eq V]

theorem mem_dom_of_mem : x :~ s ∈ Γ → x ∈ dom Γ :=
  begin
    induction Γ with hd tl ih; [simp, {cases hd, simp}],
    exact or.imp and.left ih
  end

private
lemma disjoint_forall₁ : disjoint Γ₁ Γ₂ → ∀ {b : binding V}, b ∈ Γ₁ → b.var ∉ dom Γ₂ :=
  begin
    induction Γ₁ with hd tl ih; [simp, {cases hd, simp}],
    exact λ ub d, ⟨ub, λ b h, ih d h⟩
  end

private
lemma disjoint_forall₂ : (∀ {b : binding V}, b ∈ Γ₁ → b.var ∉ dom Γ₂) → disjoint Γ₁ Γ₂ :=
  begin
    induction Γ₁ with hd tl ih; [simp, {cases hd, simp}],
    exact λ ub f, ⟨ub, ih f⟩
  end

theorem disjoint_forall : disjoint Γ₁ Γ₂ ↔ ∀ {b : binding V}, b ∈ Γ₁ → b.var ∉ dom Γ₂ :=
  ⟨disjoint_forall₁, disjoint_forall₂⟩

private
lemma mem_cons_of_uniq_cons'
: uniq (x₂ :~ s₂ :: Γ)
→ x₁ :~ s₁ ∈ x₂ :~ s₂ :: Γ
→ x₁ = x₂ ∧ s₁ = s₂ ∧ x₁ ∉ dom Γ ∨ x₁ :~ s₁ ∈ Γ ∧ x₁ ≠ x₂ :=
  begin
    simp,
    intros b u h,
    exact match h with
      | or.inl ⟨h₁, h₂⟩ := or.inl ⟨h₁, ⟨h₂, eq.rec_on h₁.symm b⟩⟩
      | or.inr h        := or.inr ⟨h, ne_of_mem_of_not_mem (mem_dom_of_mem h) b⟩
    end
  end

theorem mem_cons_of_uniq_cons
: uniq (x₂ :~ s₂ :: Γ)
→ (x₁ :~ s₁ ∈ x₂ :~ s₂ :: Γ ↔ x₁ = x₂ ∧ s₁ = s₂ ∧ x₁ ∉ dom Γ ∨ x₁ :~ s₁ ∈ Γ ∧ x₁ ≠ x₂) :=
  λ u, ⟨mem_cons_of_uniq_cons' u, by simp; exact or.imp (λ h, ⟨h.1, h.2.1⟩) and.left⟩

private
lemma mem_append_of_uniq_append'
: uniq (Γ₁ ++ Γ₂)
→ x :~ s ∈ Γ₁ ++ Γ₂
→ x :~ s ∈ Γ₁ ∧ x ∉ dom Γ₂ ∨ x ∉ dom Γ₁ ∧ x :~ s ∈ Γ₂ :=
  begin
    simp,
    intros _ _ d,
    exact or.imp (λ b, ⟨b, disjoint_forall.mp d b⟩)
                 (λ b, ⟨disjoint_forall.mp d.symm b, b⟩)
  end

theorem mem_append_of_uniq_append
: uniq (Γ₁ ++ Γ₂)
→ (x :~ s ∈ Γ₁ ++ Γ₂ ↔ x :~ s ∈ Γ₁ ∧ x ∉ dom Γ₂ ∨ x ∉ dom Γ₁ ∧ x :~ s ∈ Γ₂) :=
  λ u, ⟨mem_append_of_uniq_append' u, list.mem_append.mpr ∘ or.imp and.left and.right⟩

end /- section -/ mem ----------------------------------------------------------

end /- namespace -/ binding_list -----------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
