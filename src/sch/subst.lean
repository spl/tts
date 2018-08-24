import .core
import typ
import data.finset.fresh

namespace tts ------------------------------------------------------------------
namespace sch ------------------------------------------------------------------
variables {n : ℕ} -- Natural numbers
variables {V : Type} -- Type of variable names
variables {x x₁ x₂ : V} -- Variable names
variables {xs : list V} -- List of variable names
variables {t t₁ t₂ : typ V} -- Types
variables {ts : list (typ V)} -- Lists of types
variables {s : sch V} -- Schemes

variables [_root_.decidable_eq V]

-- Substitution with a fresh name is the identity
theorem subst_fresh (h : x ∉ fv s) : subst x t s = s :=
  by cases s; rw [subst, typ.subst_fresh h]

-- Fold typ.subst into sch.subst
theorem subst_fold : sch.mk n (typ.subst x t₂ t₁) = subst x t₂ (sch.mk n t₁) :=
  rfl

-- Substitution distributes over open
theorem subst_open (lc_t : typ.lc t)
: typ.subst x t (sch.open ts s) = sch.open (list.map (typ.subst x t) ts) (subst x t s) :=
  by cases s; unfold sch.open; rw [subst, typ.subst_open lc_t]

-- Substitution distributes over open_vars
theorem subst_open_vars (p : x ∉ xs) (lc_t : typ.lc t)
: open_vars xs (subst x t s) = typ.subst x t (open_vars xs s) :=
  by cases s; unfold open_vars; rw [subst, typ.subst_open_vars p lc_t]

@[simp]
theorem subst_arity : (subst x t s).arity = s.arity :=
  by unfold subst

-- A scheme substituted with a type is well-formed if the scheme is well-formed
-- and the type is locally-closed.
theorem subst_well_formed (lc_t : typ.lc t) (wf_s : well_formed s)
: well_formed (subst x t s) :=
  begin
    cases wf_s with L wf,
    existsi L ∪ {x},
    intros xs nd ln dj,
    simp at dj,
    rw subst_open_vars dj.2 lc_t,
    exact typ.subst_lc lc_t (wf nd (by rwa subst_arity at ln) dj.1),
  end

-- Opening up a scheme `s` with `ts` is the same as opening up `s` with fresh
-- names `xs` and then substituting `xs` for `ts`.
theorem subst_list_intro
(nd_xs : xs.nodup)
(ln_xs_ts : xs.length = ts.length)
(fr_xs : finset.disjoint_list xs (fv s ∪ typ.fv_list ts))
(lc_ts : ∀ t ∈ ts, typ.lc t)
: sch.open ts s = typ.subst_list xs ts (open_vars xs s) :=
  by unfold sch.open sch.open_vars;
     exact typ.subst_list_intro nd_xs ln_xs_ts fr_xs lc_ts

end /- namespace -/ sch --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
