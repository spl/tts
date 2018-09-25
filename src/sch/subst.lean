import .core
import typ

namespace tts ------------------------------------------------------------------
namespace sch ------------------------------------------------------------------
variables {n : ℕ} -- Natural numbers
variables {V : Type} -- Type of variable names
variables {x x₁ x₂ : tagged V} -- Variables
variables {xs : list (tagged V)} -- List of variable names
variables {t t₁ t₂ : typ V} -- Types
variables {ts : list (typ V)} -- Lists of types
variables {s : sch V} -- Schemes

variables [_root_.decidable_eq V]

-- Substitution with a fresh name is the identity
@[simp]
theorem subst_fresh (h : x ∉ fv s) : subst x t s = s :=
  eq_of_veq rfl $ typ.subst_fresh h

-- Fold typ.subst into sch.subst
theorem subst_fold : mk n (typ.subst x t₂ t₁) = subst x t₂ (mk n t₁) :=
  rfl

-- Substitution distributes over open
theorem subst_open (l : typ.lc t)
: typ.subst x t (open_typs ts s) = open_typs (list.map (typ.subst x t) ts) (subst x t s) :=
  by cases s; simp [typ.subst_open l]

-- Substitution distributes over open_vars
theorem subst_open_vars (h : x ∉ xs) (l : typ.lc t)
: open_vars xs (subst x t s) = typ.subst x t (open_vars xs s) :=
  by cases s; simp [typ.subst_open_vars h l]

@[simp]
theorem subst_arity : (subst x t s).arity = s.arity :=
  by unfold subst

@[simp]
theorem subst_type : (subst x t s).type = typ.subst x t s.type :=
  by unfold subst

-- A scheme substituted with a type is well-formed if the scheme is well-formed
-- and the type is locally-closed.
theorem subst_well_formed (lt : typ.lc t) (ls : lc s) : lc (subst x t s) :=
  begin
    cases ls with L ls,
    existsi insert x L,
    intros xs d ln_eq F,
    simp [not_or_distrib] at F,
    have h₁ : x ∉ xs := λ h, absurd (eq.refl x) (F h).1,
    have h₂ : ∀ x ∈ xs, x ∉ L := λ _ h, (F h).2,
    simp [typ.subst_open_vars h₁ lt, typ.subst_lc lt (ls d ln_eq h₂)],
  end

-- Opening up a scheme `s` with `ts` is the same as opening up `s` with fresh
-- names `xs` and then substituting `xs` for `ts`.
theorem subst_list_intro
(d : xs.nodup)
(ln_eq : xs.length = ts.length)
(F : ∀ x ∈ xs, x ∉ fv s ∪ typ.fv_list ts)
(l : ∀ t ∈ ts, typ.lc t)
: open_typs ts s = typ.subst_list xs ts (open_vars xs s) :=
  by unfold open_typs open_vars;
     exact typ.subst_list_intro d ln_eq F l

end /- namespace -/ sch --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
