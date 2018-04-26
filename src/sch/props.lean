import .defs
import typ.props
import data.finset.fresh

namespace tts ------------------------------------------------------------------
namespace sch ------------------------------------------------------------------
variables {n : ℕ}
variables {V : Type} -- Type of variable names
variables {x x₁ x₂ : V} -- Variable names
variables {xs : list V} -- List of variable names
variables {t t₁ t₂ : typ V} -- Types
variables {ts : list (typ V)} -- Lists of types
variables {s : sch V} -- Schemes
variables [_root_.decidable_eq V] [finset.has_fresh V]

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

-- A well-formed schema opened with a list of types is locally-closed if all
-- types are locally-closed.
theorem open_lc
(wf_s : well_formed s)
(len_s_ts : s.arity = ts.length)
(lc_ts : list.all_prop typ.lc ts)
: typ.lc (sch.open ts s) :=
  begin
    unfold sch.open,
    cases wf_s with L wf,
    let L := typ.fv (s.type) ∪ typ.fv_list ts ∪ L,
    let nd := finset.fresh_list_nodup L ts.length,
    let ln := finset.fresh_list_length L ts.length,
    let dj := finset.fresh_list_disjoint_union.mp (finset.fresh_list_disjoint L ts.length),
    rw typ.subst_list_intro nd ln dj.1 lc_ts,
    rw len_s_ts at wf,
    exact typ.subst_list_lc ln lc_ts (wf nd ln dj.2)
  end

end /- namespace -/ sch --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
