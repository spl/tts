import .defs
import data.multiset.extra

namespace tts ------------------------------------------------------------------
namespace env ------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {x x₁ x₂ : V} -- Variable names
variables {s s₁ s₂ : sch V} -- Type schemes
variables {fs : sch V → sch V} -- Type scheme function
variables {b : V × sch V} -- Bindings
variables {Γ Γ₁ Γ₂ Γ₃ : env V} -- Environments

/- Keep and-chains right-associated. -/
local attribute [simp] and.assoc

--------------------------------------------------------------------------------

/- Basic properties of append -/
section append_basic -----------------------------------------------------------

@[simp]
theorem append_nil_left : [] ++ Γ = Γ :=
  rfl

@[simp]
theorem append_nil_right : Γ ++ [] = Γ :=
  by simp

@[simp]
theorem append_cons : b :: Γ₁ ++ Γ₂ = b :: (Γ₁ ++ Γ₂) :=
  rfl

/-
-- TODO: I don't think this is needed.
@[simp]
theorem cons_append_one : list.cons (binding x s) Γ = one x s ++ Γ :=
  rfl
-/

end /- section -/ append_basic -------------------------------------------------

/- Basic properties of mem -/
section mem_basic --------------------------------------------------------------

@[simp]
theorem mem_nil : b ∈ ([] : env V) ↔ false :=
  by simp

@[simp]
theorem mem_one : binding x₁ s₁ ∈ one x₂ s₂ ↔ x₁ = x₂ ∧ s₁ = s₂ :=
  by simp [binding, one, list.mem_singleton]

@[simp]
theorem mem_append : b ∈ Γ₁ ++ Γ₂ ↔ b ∈ Γ₁ ∨ b ∈ Γ₂ :=
  list.mem_append

end /- section -/ mem_basic ----------------------------------------------------

/- Basic properties of map -/
section map_basic --------------------------------------------------------------
local attribute [simp] map

@[simp]
theorem map_nil : map fs [] = [] :=
  rfl

@[simp]
theorem map_cons : map fs (b :: Γ) = binding b.1 (fs b.2) :: map fs Γ :=
  by cases b; refl

@[simp]
theorem map_one : map fs (one x s) = one x (fs s) :=
  rfl

@[simp]
theorem map_append : map fs (Γ₁ ++ Γ₂) = map fs Γ₁ ++ map fs Γ₂ :=
  by simp [list.map_append]

end /- section -/ map_basic ----------------------------------------------------

/- Basic properties of dom -/
section dom_basic --------------------------------------------------------------
local attribute [simp] dom

@[simp]
theorem dom_nil : dom [] = (∅ : finset V) :=
  rfl

@[simp]
theorem dom_one : dom (one x s) = finset.singleton x :=
  rfl

@[simp]
theorem dom_cons_val : (dom (binding x s :: Γ)).val = multiset.ndinsert x (Γ.dom.val) :=
  begin
    cases Γ,
    case list.nil { simp },
    case list.cons : hd tl { cases hd, simp }
  end

@[simp]
theorem dom_cons_insert : dom (b :: Γ) = insert b.1 Γ.dom :=
  by cases b; simp

/-
-- TODO: I don't think this is needed.
@[simp]
theorem dom_cons : dom (b :: Γ) = finset.singleton b.1 ∪ Γ.dom :=
  by cases b; simp [finset.insert_eq]
-/

@[simp]
theorem dom_append : dom (Γ₁ ++ Γ₂) = Γ₁.dom ∪ Γ₂.dom :=
  by induction Γ₁ with _ _ ih; simp; simp [ih]

@[simp]
theorem dom_map : dom (Γ.map fs) = Γ.dom :=
  by induction Γ with _ _ ih; simp; simp [ih]

@[simp]
theorem mem_dom_wrap : x ∈ (dom Γ).val ↔ x ∈ dom Γ :=
  by induction Γ with hd tl ih; [simp, {cases hd, simp [ih]}]

end /- section -/ dom_basic ----------------------------------------------------

/- Basic properties of unbound -/
section unbound_basic ----------------------------------------------------------
local attribute [simp] unbound

@[simp]
theorem unbound_wrap : x ∉ (dom Γ).val ↔ Γ.unbound x :=
  by simp

theorem ne_dom_unbound : x₁ ∈ dom Γ → unbound x₂ Γ → x₁ ≠ x₂ :=
  λ h, mt $ λ e, e ▸ h

@[simp]
theorem unbound_nil : unbound x [] ↔ true :=
  iff_true_intro (by simp)

@[simp]
theorem unbound_cons : unbound x₁ (binding x₂ s :: Γ) ↔ x₁ ≠ x₂ ∧ unbound x₁ Γ :=
  by simp [decidable.not_or_iff_and_not]

@[simp]
theorem unbound_one : unbound x₁ (one x₂ s) ↔ x₁ ≠ x₂ :=
  by simp

@[simp]
theorem unbound_append : unbound x (Γ₁ ++ Γ₂) ↔ unbound x Γ₁ ∧ unbound x Γ₂ :=
  by simp [decidable.not_or_iff_and_not]

@[simp]
theorem unbound_map : unbound x (map fs Γ) ↔ unbound x Γ :=
  by simp

end /- section -/ unbound_basic ------------------------------------------------

/- Basic properties of disjoint -/
section disjoint_basic ---------------------------------------------------------

theorem disjoint_multiset : disjoint Γ₁ Γ₂ ↔ Γ₁.dom.1.disjoint Γ₂.dom.1 :=
  finset.inter_eq_empty_iff_disjoint

/- disjoint_multiset is used in nearly every simp in this section. -/
local attribute [simp] disjoint_multiset

theorem disjoint.symm : disjoint Γ₁ Γ₂ → disjoint Γ₂ Γ₁ :=
  by simp

theorem disjoint_comm : disjoint Γ₁ Γ₂ ↔ disjoint Γ₂ Γ₁ :=
  by simp

@[simp]
theorem disjoint_nil : disjoint [] Γ ↔ true :=
  iff_true_intro (by simp)

@[simp]
theorem disjoint_one_left : disjoint (one x s) Γ ↔ Γ.unbound x :=
  by simp

@[simp]
theorem disjoint_one_right : disjoint Γ (one x s) ↔ Γ.unbound x :=
  by simp

private
lemma unbound_of_disjoint_cons : disjoint (b :: Γ₁) Γ₂ → Γ₂.unbound b.1 :=
  by intro h; simp at h; exact h.1

private
lemma disjoint_of_disjoint_cons : disjoint (b :: Γ₁) Γ₂ → disjoint Γ₁ Γ₂ :=
  by simp

private
lemma disjoint_cons : Γ₂.unbound b.1 → disjoint Γ₁ Γ₂ → disjoint (b :: Γ₁) Γ₂ :=
  by simp; exact and.intro

@[simp]
theorem disjoint_cons_left : disjoint (b :: Γ₁) Γ₂ ↔ Γ₂.unbound b.1 ∧ Γ₁.disjoint Γ₂ :=
  ⟨ λ h, ⟨unbound_of_disjoint_cons h, disjoint_of_disjoint_cons h⟩
  , λ h, disjoint_cons h.1 h.2
  ⟩

@[simp]
theorem disjoint_cons_right : disjoint Γ₁ (b :: Γ₂) ↔ Γ₁.unbound b.1 ∧ Γ₁.disjoint Γ₂ :=
  by simp

@[simp]
theorem disjoint_append_left : disjoint (Γ₁ ++ Γ₂) Γ₃ ↔ disjoint Γ₁ Γ₃ ∧ disjoint Γ₂ Γ₃ :=
  by simp

@[simp]
theorem disjoint_append_right : disjoint Γ₁ (Γ₂ ++ Γ₃) ↔ disjoint Γ₁ Γ₂ ∧ disjoint Γ₁ Γ₃ :=
  by simp

@[simp]
theorem disjoint_map_left : disjoint (map fs Γ₁) Γ₂ ↔ disjoint Γ₁ Γ₂ :=
  by simp

@[simp]
theorem disjoint_map_right : disjoint Γ₁ (map fs Γ₂) ↔ disjoint Γ₁ Γ₂ :=
  by simp

end /- section -/ disjoint_basic -----------------------------------------------

/- Basic properties of uniq -/
section uniq_basic -------------------------------------------------------------

@[simp]
theorem uniq_empty : uniq ([] : env V) ↔ true :=
  iff_true_intro uniq.empty

@[simp]
theorem uniq_one : uniq (one x s) ↔ true :=
  iff_true_intro (uniq.push x s [] (unbound_nil.mpr trivial) uniq.empty)

private
lemma uniq_head_unbound : uniq (binding x s :: Γ) → Γ.unbound x :=
  by intro u; cases u; assumption

private
lemma uniq_tail_uniq : uniq (b :: Γ) → Γ.uniq :=
  by intro u; cases u; assumption

private
lemma uniq_cons : Γ.unbound x → Γ.uniq → uniq (binding x s :: Γ) :=
  by apply uniq.push

@[simp]
theorem uniq_cons_iff_unbound_head_uniq_tail : uniq (binding x s :: Γ) ↔ Γ.unbound x ∧ Γ.uniq :=
  ⟨λ u, ⟨uniq_head_unbound u, uniq_tail_uniq u⟩, λ ⟨h₁, h₂⟩, uniq_cons h₁ h₂⟩

private
lemma uniq_append_left : uniq (Γ₁ ++ Γ₂) → Γ₁.uniq ∧ Γ₂.uniq ∧ disjoint Γ₁ Γ₂ :=
  begin
    induction Γ₁ with hd tl ih; [simp, {cases hd, simp}],
    intros ub₁ ub₂ u,
    have p : uniq tl ∧ uniq Γ₂ ∧ disjoint tl Γ₂ := ih u,
    exact ⟨ub₁, ⟨p.1, ⟨p.2.1, ⟨ub₂, p.2.2⟩⟩⟩⟩
  end

private
lemma uniq_append_right : Γ₁.uniq ∧ Γ₂.uniq ∧ disjoint Γ₁ Γ₂ → uniq (Γ₁ ++ Γ₂) :=
  begin
    intro h, rcases h with ⟨u₁, u₂, d⟩,
    induction Γ₁,
    case list.nil { simpa },
    case list.cons : hd tl ih {
      cases hd, simp at u₁, simp at d, simp,
      exact ⟨u₁.1, ⟨d.1, ih u₁.2 d.2⟩⟩
    }
  end

@[simp]
theorem uniq_append : uniq (Γ₁ ++ Γ₂) ↔ Γ₁.uniq ∧ Γ₂.uniq ∧ disjoint Γ₁ Γ₂ :=
  ⟨uniq_append_left, uniq_append_right⟩

@[simp]
theorem uniq_map : uniq (map fs Γ) ↔ uniq Γ :=
  by induction Γ with hd tl ih; [simp, {cases hd, simp [ih]}]

end /- section -/ uniq_basic ---------------------------------------------------

/- Basic properties of binds -/
section binds_basic ------------------------------------------------------------
local attribute [simp] binds prod.map

@[simp]
theorem binds_nil : binds x s [] ↔ false :=
  by simp

@[simp]
theorem binds_one : binds x₁ s₁ (one x₂ s₂) ↔ x₁ = x₂ ∧ s₁ = s₂ :=
  by simp

@[simp]
theorem binds_cons : binds x₁ s₁ (binding x₂ s₂ :: Γ) ↔ x₁ = x₂ ∧ s₁ = s₂ ∨ binds x₁ s₁ Γ :=
  by simp

@[simp]
theorem binds_append : binds x s (Γ₁ ++ Γ₂) ↔ binds x s Γ₁ ∨ binds x s Γ₂ :=
  by simp

theorem binds_map₁ : function.injective fs → binds x (fs s) (map fs Γ) → binds x s Γ :=
  begin
    intro fs_inj,
    cases Γ with hd tl; [simp, {cases hd, simp}],
    intro h, cases h,
    case or.inl : h {
      cases h with h₁ h₂,
      exact or.inl ⟨h₁, fs_inj h₂⟩
    },
    case or.inr : h {
      rcases h with ⟨u₁, u₂, h₁, h₂, h₃⟩,
      subst h₂,
      have h₄ : u₂ = s := fs_inj h₃,
      subst h₄,
      exact or.inr h₁,
    }
  end

theorem binds_map₂ : binds x s₁ (map fs Γ) → ∃ s₂, fs s₂ = s₁ ∧ binds x s₂ Γ :=
  begin
    cases Γ with hd tl; [simp, {cases hd with _ s₂, simp}],
    intro h, cases h,
    case or.inl : h {
      cases h with h₁ h₂,
      exact ⟨s₂, ⟨h₂.symm, or.inl ⟨h₁, rfl⟩⟩⟩
    },
    case or.inr : h {
      rcases h with ⟨_, s₃, h₁, h₂, h₃⟩,
      subst h₂,
      exact ⟨s₃, ⟨h₃, or.inr h₁⟩⟩
    }
  end

theorem binds_map₃ : binds x s Γ → binds x (fs s) (map fs Γ) :=
  begin
    cases Γ with hd tl; [simp, {cases hd, simp}],
    intro h, cases h,
    case or.inl : h {
      cases h with h₁ h₂,
      exact or.inl ⟨h₁, congr_arg fs h₂⟩
    },
    case or.inr : h {
      exact or.inr ⟨x, ⟨s, ⟨h, by simp [prod.map]⟩⟩⟩
    }
  end

theorem binds_dom : binds x s Γ → x ∈ dom Γ :=
  begin
    induction Γ with hd tl ih; [simp, {cases hd, simp}],
    exact or.imp and.left ih
  end

theorem unbound_of_binds_disjoint : disjoint Γ₁ Γ₂ → binds x s Γ₁ → unbound x Γ₂ :=
  begin
    induction Γ₁ with hd tl ih; [simp, {cases hd, simp}],
    intros u d b,
    exact match b with
      | or.inl ⟨h, _⟩ := eq.rec_on h.symm u
      | or.inr h      := ih d h
    end
  end

private
lemma binds_append_uniq₁
: uniq (Γ₁ ++ Γ₂) → binds x s (Γ₁ ++ Γ₂)
→ binds x s Γ₁ ∧ unbound x Γ₂ ∨ unbound x Γ₁ ∧ binds x s Γ₂ :=
  begin
    simp,
    intros _ _ d,
    exact or.imp (λ b, ⟨b, unbound_of_binds_disjoint d b⟩) (λ b, ⟨unbound_of_binds_disjoint d.symm b, b⟩)
  end

theorem binds_append_uniq
: uniq (Γ₁ ++ Γ₂)
→ (binds x s (Γ₁ ++ Γ₂) ↔ binds x s Γ₁ ∧ unbound x Γ₂ ∨ unbound x Γ₁ ∧ binds x s Γ₂) :=
  λ u, ⟨binds_append_uniq₁ u, binds_append.mpr ∘ or.imp and.left and.right⟩

private
lemma binds_cons_uniq₁
: uniq (binding x₂ s₂ :: Γ)
→ binds x₁ s₁ (binding x₂ s₂ :: Γ)
→ x₁ = x₂ ∧ s₁ = s₂ ∧ unbound x₁ Γ ∨ binds x₁ s₁ Γ ∧ x₁ ≠ x₂ :=
  begin
    simp,
    intros b u h,
    exact match h with
      | or.inl ⟨h₁, h₂⟩ := or.inl ⟨h₁, ⟨h₂, eq.rec_on h₁.symm b⟩⟩
      | or.inr h        := or.inr ⟨h, ne_dom_unbound (binds_dom h) b⟩
    end
  end

theorem binds_cons_uniq
: uniq (binding x₂ s₂ :: Γ)
→ (binds x₁ s₁ (binding x₂ s₂ :: Γ) ↔ x₁ = x₂ ∧ s₁ = s₂ ∧ unbound x₁ Γ ∨ binds x₁ s₁ Γ ∧ x₁ ≠ x₂) :=
  λ u, ⟨binds_cons_uniq₁ u, by simp; exact or.imp (λ h, ⟨h.1, h.2.1⟩) and.left⟩

end /- section -/ binds_basic --------------------------------------------------

end /- namespace -/ env --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
