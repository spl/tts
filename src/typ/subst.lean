import .fv
import .lc
import typ.open
import data.finset
import logic.extra

local attribute [simp] not_or_distrib and_assoc


namespace tts ------------------------------------------------------------------
namespace typ ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {x y : tagged V} -- Variables
variables {xs : list (tagged V)} -- List of variable names
variables {t tx t₁ t₂ : typ V} -- Types
variables {ts ts₁ ts₂ : list (typ V)} -- Lists of types

variables [_root_.decidable_eq V]

open occurs

@[simp]
theorem subst_var_bound : subst x t (var bound y) = var bound y :=
  rfl

@[simp]
theorem subst_var_free_eq (h : x = y) : subst x t (var free y) = t :=
  by simp [subst, h]

@[simp]
theorem subst_var_free_ne (h : x ≠ y) : subst x t (var free y) = var free y :=
  by simp [subst, h]

@[simp]
theorem subst_arr {t₁ t₂ : typ V} : subst x t (arr t₁ t₂) = arr (subst x t t₁) (subst x t t₂) :=
  rfl

@[simp]
theorem subst_list_nil_left : subst_list [] ts t = t :=
  rfl

@[simp]
theorem subst_list_nil_right : subst_list xs [] t = t :=
  by cases xs; refl

@[simp]
theorem subst_list_cons_cons : subst_list (x :: xs) (tx :: ts) t = subst_list xs ts (subst x tx t) :=
  rfl

-- Substitution with a fresh name is the identity
@[simp]
theorem subst_fresh (h : x ∉ fv t) : subst x tx t = t :=
  by induction t with o; try {cases o}; try {simp at h}; try {cases h}; simp *

-- Mapping substitution over a list with a fresh name is the identity
@[simp]
theorem subst_fresh_list (h : x ∉ fv_list ts) : list.map (subst x t) ts = ts :=
  begin
/-
    induction ts with _ _ ih; simp [decidable.not_or_iff_and_not],
    exact λ h₁ h₂, ⟨subst_fresh h₁, ih h₂⟩
-/
    induction ts; try {simp at h}; try {cases h}; simp *
  end

@[simp]
theorem subst_fresh_var_free (h : x ∉ xs)
: list.map (subst x t) (list.map (var free) xs) = list.map (var free) xs :=
  begin
    apply subst_fresh_list,
    induction xs with _ _ ih; simp,
    exact ⟨list.ne_of_not_mem_cons h, ih (list.not_mem_of_not_mem_cons h)⟩
  end

@[simp]
theorem subst_list_fresh (F : ∀ x ∈ xs, x ∉ fv t) : subst_list xs ts t = t :=
  begin
    induction xs generalizing ts t,
    case list.nil { simp },
    case list.cons : _ _ ih { simp at F, cases ts; [simp, {simp [F.1, ih F.2]}] }
  end

-- Substitution distributes over open
theorem subst_open (l₂ : lc t₂)
: subst x t₂ (open_typs ts t₁) = open_typs (list.map (subst x t₂) ts) (subst x t₂ t₁) :=
  begin
    induction t₁,
    case typ.var : o y {
      cases o,
      case occurs.bound { simp [list.nth_of_map] },
      case occurs.free  { by_cases x = y; simp * }
    },
    case typ.arr { simp * }
  end

-- Substitution and open_vars for distinct names commute
theorem subst_open_vars (h : x ∉ xs) (l₂ : lc t₂)
: open_vars xs (subst x t₂ t₁) = subst x t₂ (open_vars xs t₁) :=
  by simp [open_vars, h, subst_open l₂]

theorem subst_list_intro_aux
(ts₂ : list (typ V))
(d : xs.nodup)
(ln_eq : xs.length = ts₁.length)
(F : ∀ x ∈ xs, x ∉ fv t ∪ fv_list ts₁ ∪ fv_list ts₂)
(l₁ : ∀ t ∈ ts₁, lc t)
(l₂ : ∀ t ∈ ts₂, lc t)
: open_typs (ts₂ ++ ts₁) t = subst_list xs ts₁ (open_typs (ts₂ ++ list.map (var free) xs) t) :=
  begin
    induction xs generalizing ts₁ ts₂ d,
    case list.nil {
      have : ts₁ = [] := list.length_eq_zero.mp (by simp at ln_eq; simp [ln_eq]),
      simp [this]
    },
    case list.cons : hd tl ih {
      cases ts₁; simp at ln_eq,
      case list.nil { cases ln_eq },
      case list.cons : hd₁ tl₁ {
        simp at l₁,
        have lhd₁ : lc hd₁ := l₁.1,
        have ltl₁ : ∀ t ∈ tl₁, lc t := l₁.2,
        clear l₁,
        simp at F,
        have hdFt   : hd ∉ fv t := F.1,
        have hdFhd₁ : hd ∉ fv hd₁ := F.2.1,
        have hdFts₂ : hd ∉ fv_list ts₂ := F.2.2.1,
        have hdFts₂hd₁ : hd ∉ fv_list (ts₂ ++ [hd₁]),
          by simp [hdFhd₁, hdFts₂],
        have tlF    : ∀ x ∈ tl, x ∉ fv t ∪ fv_list tl₁ ∪ fv_list (ts₂ ++ [hd₁]) :=
          λ x h, let H := F.2.2.2.2 x h in by simp [H.1, H.2.1, H.2.2.1, H.2.2.2],
        clear hdFhd₁ F,
        have lts₂hd₁ : ∀ t ∈ ts₂ ++ [hd₁], lc t :=
          λ t h, by simp at h; cases h; simp [h, l₂ t, lhd₁],
        simp at d,
        have ih : open_typs (ts₂ ++ [hd₁] ++ tl₁) t =
        subst_list tl tl₁ (open_typs (ts₂ ++ [hd₁] ++ list.map (var free) tl) t) :=
          ih _ d.2 ln_eq tlF ltl₁ lts₂hd₁,
        rw [list.append_cons_left, ih, ←list.append_cons_left],
        simp [subst_open lhd₁, subst_fresh hdFt, subst_fresh_list hdFts₂, subst_fresh_var_free d.1]
      },
    }
  end

-- Opening up a type `t` with `ts` is the same as opening up `t` with fresh
-- names `xs` and then substituting `xs` for `ts`.
theorem subst_list_intro
(d : xs.nodup)
(ln_eq : xs.length = ts.length)
(F : ∀ x ∈ xs, x ∉ fv t ∪ fv_list ts)
(l : ∀ t ∈ ts, lc t)
: open_typs ts t = subst_list xs ts (open_vars xs t) :=
  subst_list_intro_aux [] d ln_eq (λ x, by simpa using F x) l (by simp)

-- A type substituted with another type is locally-closed if all type arguments
-- are locally-closed.
theorem subst_lc (l₂ : lc t₂) (l₁ : lc t₁) : lc (subst x t₂ t₁) :=
  begin
    induction l₁,
    case lc.var : y { by_cases h : x = y; simp [h, l₂] },
    case lc.arr { simp * }
  end

-- A type substituted with a list of types is locally-closed if all type
-- arguments are locally-closed.
theorem subst_list_lc
(ln_eq : xs.length = ts.length)
(lts : ∀ t ∈ ts, lc t)
(lt : lc t)
: lc (subst_list xs ts t) :=
  begin
    induction xs generalizing ts t,
    case list.nil { simp [lt] },
    case list.cons : _ _ ih {
      cases ts,
      case list.nil { simp [lt] },
      case list.cons {
        simp at ln_eq,
        simp at lts,
        simp [ih ln_eq lts.2 (subst_lc lts.1 lt)]
      }
    }
  end

-- Mapping substitution over a list of types is locally-closed if all type
-- arguments are locally-closed.
theorem map_subst_lc (lt : lc t) (lts : ∀ t ∈ ts, lc t)
: ∀ t ∈ list.map (subst x t) ts, lc t :=
  begin
    induction ts,
    case list.nil { simp },
    case list.cons : _ _ ih {
      simp at lts,
      exact list.forall_mem_cons.mpr ⟨subst_lc lt lts.1, ih lts.2⟩
    }
  end

end /- namespace -/ typ --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
