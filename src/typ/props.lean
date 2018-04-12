import .defs
import fresh
import logic.extra

namespace tts ------------------------------------------------------------------
namespace typ ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {x x₁ x₂ : V} -- Variable names
variables {xs : list V} -- List of variable names
variables {t t₁ t₂ : typ V} -- Types
variables {ts ts₁ ts₂ : list (typ V)} -- Lists of types

-- Opening a locally-closed type is the identity
theorem open_of_lc (p : lc t) : typ.open ts t = t :=
  by induction t; cases p; simp [typ.open, *]

variables [_root_.decidable_eq V]

@[simp]
theorem fv.not_mem_varf : x₁ ∉ fv (varf x₂) ↔ x₁ ≠ x₂ :=
  by simp [fv]

@[simp]
theorem fv.not_mem_arr : x ∉ fv (arr t₁ t₂) ↔ x ∉ fv t₁ ∧ x ∉ fv t₂ :=
  by simp [fv, decidable.not_or_iff_and_not]

@[simp]
theorem fv_list_nil : fv_list (@list.nil (typ V)) = ∅ :=
  rfl

@[simp]
theorem fv_list_cons : fv_list (t :: ts) = fv t ∪ fv_list ts :=
  rfl

@[simp]
theorem fv_list_append : fv_list (ts₁ ++ ts₂) = fv_list ts₁ ∪ fv_list ts₂ :=
  by induction ts₁ with _ _ ih; [simp, simp [ih]]

-- Substitution with a fresh name is the identity
theorem subst_fresh : x ∉ fv t₁ → subst x t₂ t₁ = t₁ :=
  begin
    intro p,
    induction t₁; rw subst; simp at p,
    case typ.varf : y {
      rw if_neg (ne.symm p)
    },
    case typ.arr : t₁ t₂ ih₁ ih₂ {
      rw [ih₁ p.1, ih₂ p.2]
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

theorem subst_list_fresh (p : fresh (fv t) xs) : subst_list xs ts t = t :=
  begin
    induction xs with _ _ ih generalizing ts t; [skip, cases ts]; simp [subst_list],
    simp [fresh] at p,
    rw [subst_fresh p.2.1, ih p.2.2]
  end


-- Substitution distributes over open
theorem subst_open (lc_t₂ : lc t₂)
: subst x t₂ (typ.open ts t₁) = typ.open (list.map (subst x t₂) ts) (subst x t₂ t₁) :=
  begin
    induction t₁; simp [typ.open],
    case typ.varb : n {
      simp [subst, list.nth_of_map, typ.open]
    },
    case typ.varf : y {
      simp [subst, if_distrib (typ.open (list.map (subst x t₂) ts)), open_of_lc lc_t₂],
      congr
    },
    case typ.arr : t₁ t₂ ih₁ ih₂ {
      simp [subst, ih₁, ih₂, typ.open]
    }
  end

-- Substitution and open_vars for distinct names commute
theorem subst_open_vars (p : x ∉ xs) (lc_t₂ : lc t₂)
: open_vars xs (subst x t₂ t₁) = subst x t₂ (open_vars xs t₁) :=
  by unfold open_vars; rw [subst_open lc_t₂, subst_fresh_varf p]

theorem subst_list_intro.rec
(fr_xs : fresh (fv t ∪ fv_list ts₁ ∪ fv_list ts₂) xs)
(len_xs_ts₁ : list.length xs = list.length ts₁)
(lc_ts₁ : list.all_prop lc ts₁)
(lc_ts₂ : list.all_prop lc ts₂)
: t.open (ts₂ ++ ts₁) = subst_list xs ts₁ (t.open (ts₂ ++ xs.map varf)) :=
  begin
    induction xs with hd tl ih generalizing ts₁ ts₂; simp;
      simp [fresh, decidable.not_or_iff_and_not, and.assoc] at fr_xs,
    begin
      rw list.length at len_xs_ts₁,
      have ts₁_nil : ts₁ = [] := list.eq_nil_of_length_eq_zero len_xs_ts₁.symm,
      subst ts₁_nil,
      simp [subst_list]
    end,
    begin
      rcases fr_xs with
        ⟨ hd_nin_tl, hd_nin_fv_t, hd_nin_fv_list_t₁, hd_nin_fv_list_t₂
        , fresh_fv_t_tl, fresh_fv_list_ts₁_tl, fresh_fv_list_ts₂_tl
        ⟩,
      cases ts₁; simp at len_xs_ts₁,
      case list.nil { cases nat.eq_zero_of_add_eq_zero_right len_xs_ts₁ },
      case list.cons : hd₁ tl₁ {
        cases lc_ts₁ with _ _ lc_hd₁ lc_tl₁,
        have lc_ts₂' : list.all_prop lc (ts₂ ++ [hd₁]) :=
          list.all_prop.append lc_ts₂ (list.all_prop.singleton lc_hd₁),
        simp at fresh_fv_list_ts₁_tl,
        cases fresh_fv_list_ts₁_tl with fresh_fv_hd₁_tl fresh_fv_list_tl₁_tl,
        have : fresh (fv_list (ts₂ ++ [hd₁])) tl, by simp;
          exact ⟨fresh_fv_hd₁_tl, fresh_fv_list_ts₂_tl⟩,
        have fr_tl : fresh (fv t ∪ fv_list tl₁ ∪ fv_list (ts₂ ++ [hd₁])) tl :=
          fresh_union.mpr ⟨fresh_union.mpr ⟨fresh_fv_t_tl, fresh_fv_list_tl₁_tl⟩, this⟩,
        simp [subst_list],
        rw subst_open lc_hd₁,
        have : typ.open (ts₂ ++ [hd₁] ++ tl₁) t = subst_list tl tl₁ (typ.open (ts₂ ++ [hd₁] ++ list.map varf tl) t) :=
          ih fr_tl len_xs_ts₁ lc_tl₁ lc_ts₂',
        rw [list.append_cons_left, this, ←list.append_cons_left],
        rw subst_fresh hd_nin_fv_t,
        rw list.map_append (subst hd hd₁),
        rw subst_fresh_list hd_nin_fv_list_t₂,
        rw list.map,
        rw subst_fresh_varf hd_nin_tl,
        simp [subst]
      }
    end
  end

-- Opening up a term `t` with `ts` is the same as opening up `t` with fresh
-- names `xs` and then substituting `xs` for `ts`.
theorem subst_list_intro
(fr_xs : fresh (fv t ∪ fv_list ts) xs)
(len_xs_ts : list.length xs = list.length ts)
(lc_ts : list.all_prop lc ts)
: typ.open ts t = subst_list xs ts (typ.open (list.map varf xs) t) :=
  @subst_list_intro.rec _ xs t ts [] _
    (by simp at fr_xs; simp [fr_xs])
    len_xs_ts
    lc_ts
    (by constructor)

-- A type substituted with another type is locally-closed if all type arguments
-- are locally-closed.
theorem subst_lc (l₂ : lc t₂) (l₁ : lc t₁) : lc (subst x t₂ t₁) :=
  begin
    induction l₁; simp [subst],
    case lc.varf : y { by_cases h : y = x; simp [h], exact l₂, exact lc.varf y },
    case lc.arr : _ _ _ _ ih₁ ih₂ { exact lc.arr ih₁ ih₂ }
  end

-- A type substituted with a list of types is locally-closed if all type
-- arguments are locally-closed.
theorem subst_list_lc
(len_xs_ts : list.length xs = list.length ts)
(lc_ts : list.all_prop lc ts)
(lc_t : lc t)
: lc (subst_list xs ts t) :=
  begin
    induction xs with _ _ ih generalizing ts t; cases ts; simp [subst_list];
      try { assumption },
    cases lc_ts with _ _ lc_ts_hd lc_ts_tl,
    exact ih (list.length_tail_eq_length_tail len_xs_ts) lc_ts_tl
      (subst_lc lc_ts_hd lc_t)
  end

-- Mapping substitution over a list of types is locally-closed if all type
-- arguments are locally-closed.
theorem map_subst_lc
(lc_t : lc t)
(lc_ts : list.all_prop lc ts)
: list.all_prop lc (list.map (subst x t) ts) :=
  begin
    induction ts with _ _ ih; simp [list.map],
    cases lc_ts with _ _ lc_ts_hd lc_ts_tl,
    exact ⟨subst_lc lc_t lc_ts_hd, ih lc_ts_tl⟩
  end

end /- namespace -/ typ --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
