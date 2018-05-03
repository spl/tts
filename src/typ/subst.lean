import .fv
import .lc
import typ.open
import data.finset.disjoint_list
import logic.extra

namespace tts ------------------------------------------------------------------
namespace typ ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {x x₁ x₂ : V} -- Variable names
variables {xs : list V} -- List of variable names
variables {t t₁ t₂ : typ V} -- Types
variables {ts ts₁ ts₂ : list (typ V)} -- Lists of types

variables [_root_.decidable_eq V]

-- Substitution with a fresh name is the identity
@[simp]
theorem subst_fresh (h : x ∉ fv t₁) : subst x t₂ t₁ = t₁ :=
  begin
    induction t₁; rw subst; simp [decidable.not_or_iff_and_not] at h,
    case typ.varf : y {
      rw if_neg (ne.symm h)
    },
    case typ.arr : t₁ t₂ ih₁ ih₂ {
      rw [ih₁ h.1, ih₂ h.2]
    }
  end

-- Mapping substitution over a list with a fresh name is the identity
theorem subst_fresh_list : x ∉ fv_list ts → list.map (subst x t) ts = ts :=
  begin
    induction ts with _ _ ih; simp [decidable.not_or_iff_and_not],
    exact λ p₁ p₂, ⟨subst_fresh p₁, ih p₂⟩
  end

@[simp]
theorem subst_fresh_varf (p : x ∉ xs)
: list.map (subst x t) (list.map varf xs) = list.map varf xs :=
  begin
    apply subst_fresh_list,
    induction xs with _ _ ih; simp [decidable.not_or_iff_and_not],
    exact ⟨list.ne_of_not_mem_cons p, ih (list.not_mem_of_not_mem_cons p)⟩
  end

theorem subst_list_fresh (p : finset.disjoint_list xs (fv t)) : subst_list xs ts t = t :=
  begin
    induction xs with _ _ ih generalizing ts t; [skip, cases ts]; simp,
    simp at p,
    rw [subst_fresh p.1, ih p.2]
  end

-- Substitution distributes over open
theorem subst_open (lc_t₂ : lc t₂)
: subst x t₂ (typ.open ts t₁) = typ.open (list.map (subst x t₂) ts) (subst x t₂ t₁) :=
  begin
    induction t₁; simp,
    case typ.varb {
      simp [list.nth_of_map]
    },
    case typ.varf {
      simp [if_distrib (typ.open (list.map (subst x t₂) ts)), open_lc lc_t₂],
      congr
    },
    case typ.arr : _ _ ih₁ ih₂ {
      simp [ih₁, ih₂]
    }
  end

-- Substitution and open_vars for distinct names commute
theorem subst_open_vars (p : x ∉ xs) (lc_t₂ : lc t₂)
: open_vars xs (subst x t₂ t₁) = subst x t₂ (open_vars xs t₁) :=
  by unfold open_vars; rw [subst_open lc_t₂, subst_fresh_varf p]

theorem subst_list_intro.rec
(nd_xs : list.nodup xs)
(len_xs_ts₁ : list.length xs = list.length ts₁)
(fr_xs : finset.disjoint_list xs (fv t ∪ fv_list ts₁ ∪ fv_list ts₂))
(lc_ts₁ : ∀ t ∈ ts₁, lc t)
(lc_ts₂ : ∀ t ∈ ts₂, lc t)
: t.open (ts₂ ++ ts₁) = subst_list xs ts₁ (t.open (ts₂ ++ list.map varf xs)) :=
  begin
    induction xs generalizing ts₁ ts₂; simp; simp [and.assoc] at fr_xs,
    case list.nil {
      rw list.length at len_xs_ts₁,
      have ts₁_nil : ts₁ = [] := list.eq_nil_of_length_eq_zero len_xs_ts₁.symm,
      subst ts₁_nil,
      simp
    },
    case list.cons : hd tl ih {
      rcases fr_xs with
        ⟨ hd_nin_fv_t, tl_nin_fv_t, hd_nin_fv_list_t₁, tl_nin_fv_list_ts₁
        , hd_nin_fv_list_t₂, tl_nin_fv_list_ts₂
        ⟩,
      cases ts₁; simp at len_xs_ts₁,
      case list.nil { cases nat.eq_zero_of_add_eq_zero_right len_xs_ts₁ },
      case list.cons : hd₁ tl₁ {
        cases list.forall_mem_cons.mp lc_ts₁ with lc_hd₁ lc_tl₁,
        have lc_ts₂' : ∀ t ∈ ts₂ ++ [hd₁], lc t :=
          list.forall_mem_append.mpr ⟨lc_ts₂, list.forall_mem_singleton lc_hd₁⟩,
        simp at tl_nin_fv_list_ts₁,
        cases tl_nin_fv_list_ts₁ with tl_nin_fv_hd₁ tl_nin_fv_list_tl₁,
        have : finset.disjoint_list tl (fv_list (ts₂ ++ [hd₁])), by
          simp; exact ⟨tl_nin_fv_hd₁, tl_nin_fv_list_ts₂⟩,
        have fr_tl : finset.disjoint_list tl (fv t ∪ fv_list tl₁ ∪ fv_list (ts₂ ++ [hd₁])) :=
          finset.disjoint_list_union.mpr ⟨finset.disjoint_list_union.mpr ⟨tl_nin_fv_t, tl_nin_fv_list_tl₁⟩, this⟩,
        simp,
        rw subst_open lc_hd₁,
        have : typ.open (ts₂ ++ [hd₁] ++ tl₁) t = subst_list tl tl₁ (typ.open (ts₂ ++ [hd₁] ++ list.map varf tl) t) :=
          ih (list.nodup_of_nodup_cons nd_xs) len_xs_ts₁ fr_tl lc_tl₁ lc_ts₂',
        rw [list.append_cons_left, this, ←list.append_cons_left],
        rw subst_fresh hd_nin_fv_t,
        rw list.map_append (subst hd hd₁),
        rw subst_fresh_list hd_nin_fv_list_t₂,
        rw list.map,
        rw subst_fresh_varf (list.not_mem_of_nodup_cons nd_xs),
        simp [subst]
      }
    }
  end

-- Opening up a term `t` with `ts` is the same as opening up `t` with fresh
-- names `xs` and then substituting `xs` for `ts`.
theorem subst_list_intro
(nd_xs : list.nodup xs)
(len_xs_ts : list.length xs = list.length ts)
(fr_xs : finset.disjoint_list xs (fv t ∪ fv_list ts))
(lc_ts : ∀ t ∈ ts, lc t)
: typ.open ts t = subst_list xs ts (typ.open_vars xs t) :=
  @subst_list_intro.rec _ xs t ts [] _
    nd_xs
    len_xs_ts
    (by simp at fr_xs; simp [fr_xs])
    lc_ts
    (by simp)

-- A type substituted with another type is locally-closed if all type arguments
-- are locally-closed.
theorem subst_lc (l₂ : lc t₂) (l₁ : lc t₁) : lc (subst x t₂ t₁) :=
  begin
    induction l₁; simp [subst],
    case lc.varf : y { by_cases h : y = x; simp [h], exact l₂ },
    case lc.arr { tauto }
  end

-- A type substituted with a list of types is locally-closed if all type
-- arguments are locally-closed.
theorem subst_list_lc
(len_xs_ts : list.length xs = list.length ts)
(lc_ts : ∀ t ∈ ts, lc t)
(lc_t : lc t)
: lc (subst_list xs ts t) :=
  begin
    induction xs with _ _ ih generalizing ts t; cases ts; simp; try { assumption },
    cases list.forall_mem_cons.mp lc_ts with lc_ts_hd lc_ts_tl,
    exact ih (list.length_tail_eq_length_tail len_xs_ts) lc_ts_tl
      (subst_lc lc_ts_hd lc_t)
  end

-- Mapping substitution over a list of types is locally-closed if all type
-- arguments are locally-closed.
theorem map_subst_lc
(lc_t : lc t)
(lc_ts : ∀ t ∈ ts, lc t)
: ∀ t ∈ list.map (subst x t) ts, lc t :=
  begin
    induction ts,
    case list.nil { simp [list.map] },
    case list.cons : _ _ ih {
      cases list.forall_mem_cons.mp lc_ts with lc_hd lc_tl,
      exact list.forall_mem_cons.mpr ⟨subst_lc lc_t lc_hd, ih lc_tl⟩
    }
  end

end /- namespace -/ typ --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
