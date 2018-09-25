import data.list.extra .fv .lc

local attribute [simp] not_or_distrib and_assoc

namespace tts ------------------------------------------------------------------
namespace typ ------------------------------------------------------------------
variables {V : Type} [_root_.decidable_eq V] -- Type of variable names
variables {x y : tagged V} -- Variables
variables {xs : list (tagged V)} -- List of variables
variables {t tx t₁ t₂ : typ V} -- Types
variables {ts txs ts₂ : list (typ V)} -- Lists of types

open list occurs

/- subst -/

/-- Substitute a free variable for a type in a type -/
def subst (x : tagged V) (tx : typ V) : typ V → typ V
| (var bound y)  := var bound y
| (var free y)   := if x = y then tx else var free y
| (arr t₁ t₂)    := arr (subst t₁) (subst t₂)

@[simp] theorem subst_var_bound : subst x tx (var bound y) = var bound y :=
rfl

@[simp] theorem subst_var_free_eq (h : x = y) : subst x tx (var free y) = tx :=
by simp [subst, h]

@[simp] theorem subst_var_free_ne (h : x ≠ y) : subst x tx (var free y) = var free y :=
by simp [subst, h]

@[simp] theorem subst_arr : subst x tx (arr t₁ t₂) = arr (subst x tx t₁) (subst x tx t₂) :=
rfl

-- Substitution with a fresh name is the identity
@[simp] theorem subst_fresh (h : x ∉ fv t) : subst x tx t = t :=
by induction t with o; try {cases o}; try {simp at h}; try {cases h}; simp *

-- Mapping substitution over a list with a fresh name is the identity
@[simp] theorem subst_fresh_list (h : x ∉ fv_list ts) : map (subst x t) ts = ts :=
by induction ts; try {simp at h}; try {cases h}; simp *

@[simp] theorem subst_fresh_var_free (h : x ∉ xs) :
  map (subst x tx) (map (var free) xs) = map (var free) xs :=
begin
  apply subst_fresh_list,
  induction xs with _ _ ih; simp,
  exact ⟨ne_of_not_mem_cons h, ih (not_mem_of_not_mem_cons h)⟩
end

/- subst_list -/

/-- Substitute a list of free variables for a list of types in a type -/
def subst_list : list (tagged V) → list (typ V) → typ V → typ V
| (x :: xs) (tx :: txs) t := subst_list xs txs (subst x tx t)
| _         _           t := t

@[simp] theorem subst_list_nil_left : subst_list [] txs t = t :=
rfl

@[simp] theorem subst_list_nil_right : subst_list xs [] t = t :=
by cases xs; refl

@[simp] theorem subst_list_cons_cons :
  subst_list (x :: xs) (tx :: txs) t = subst_list xs txs (subst x tx t) :=
rfl

@[simp] theorem subst_list_fresh (F : ∀ x ∈ xs, x ∉ fv t) : subst_list xs txs t = t :=
begin
  induction xs generalizing txs t,
  case list.nil { simp },
  case list.cons : _ _ ih { simp at F, cases txs; [simp, {simp [F.1, ih F.2]}] }
end

-- Substitution distributes over open
theorem subst_open_typs (lx : lc tx) :
  subst x tx (open_typs ts t) = open_typs (map (subst x tx) ts) (subst x tx t) :=
begin
  induction t,
  case typ.var : o y {
    cases o,
    case occurs.bound { simp [nth_of_map] },
    case occurs.free  { by_cases x = y; simp * } },
  case typ.arr { simp * }
end

-- Substitution and open_vars for distinct names commute
theorem subst_open_vars (h : x ∉ xs) (lx : lc tx) :
  open_vars xs (subst x tx t) = subst x tx (open_vars xs t) :=
by simp [open_vars, h, subst_open_typs lx]

theorem subst_list_intro_aux
  (ts : list (typ V))
  (d : xs.nodup)
  (ln_eq : xs.length = txs.length)
  (F : ∀ x ∈ xs, x ∉ fv t ∪ fv_list txs ∪ fv_list ts)
  (ltxs : ∀ t ∈ txs, lc t)
  (l₂ : ∀ t ∈ ts, lc t) :
  open_typs (ts ++ txs) t = subst_list xs txs (open_typs (ts ++ map (var free) xs) t) :=
begin
  induction xs generalizing txs ts d,
  case list.nil {
    have : txs = [] := length_eq_zero.mp (by simp at ln_eq; simp [ln_eq]),
    simp [this] },
  case list.cons : hd tl ih {
    cases txs; simp at ln_eq,
    case list.nil { cases ln_eq },
    case list.cons : hdxs tlxs {
      simp at ltxs,
      have lhdxs : lc hdxs := ltxs.1,
      have ltlxs : ∀ t ∈ tlxs, lc t := ltxs.2,
      simp at F,
      have hdFt    : hd ∉ fv t := F.1,
      have hdFhdxs : hd ∉ fv hdxs := F.2.1,
      have hdFts   : hd ∉ fv_list ts := F.2.2.1,
      have tlF     : ∀ x ∈ tl, x ∉ fv t ∪ fv_list tlxs ∪ fv_list (ts ++ [hdxs]) :=
        λ x h, let H := F.2.2.2.2 x h in by simp [H.1, H.2.1, H.2.2.1, H.2.2.2],
      have lts_hdxs : ∀ t ∈ ts ++ [hdxs], lc t :=
        λ t h, by simp at h; cases h; simp [h, l₂ t, lhdxs],
      simp at d,
      have ih : open_typs (ts ++ [hdxs] ++ tlxs) t =
      subst_list tl tlxs (open_typs (ts ++ [hdxs] ++ map (var free) tl) t) :=
        ih _ d.2 ln_eq tlF ltlxs lts_hdxs,
      have append_cons_mid : ∀ {α} {a : α} {l₁ l₂ : list α}, l₁ ++ a :: l₂ = l₁ ++ [a] ++ l₂,
        by intros; simp,
      rw [append_cons_mid, ih, ←append_cons_mid],
      simp [ih, subst_open_typs lhdxs, subst_fresh hdFt, subst_fresh_list hdFts, subst_fresh_var_free d.1] } }
end

-- Opening up a type `t` with `ts` is the same as opening up `t` with fresh
-- names `xs` and then substituting `xs` for `ts`.
theorem subst_list_intro
  (d : xs.nodup)
  (ln_eq : xs.length = ts.length)
  (F : ∀ x ∈ xs, x ∉ fv t ∪ fv_list ts)
  (l : ∀ t ∈ ts, lc t) :
  open_typs ts t = subst_list xs ts (open_vars xs t) :=
subst_list_intro_aux [] d ln_eq (λ x, by simpa using F x) l (by simp)

-- A type substituted with another type is locally-closed if all type arguments
-- are locally-closed.
theorem subst_lc (lx : lc tx) (l : lc t) : lc (subst x tx t) :=
begin
  induction l,
  case lc.var : y { by_cases h : x = y; simp [h, lx] },
  case lc.arr { simp * }
end

-- A type substituted with a list of types is locally-closed if all type
-- arguments are locally-closed.
theorem subst_list_lc
  (ln_eq : xs.length = txs.length)
  (ltxs : ∀ tx ∈ txs, lc tx)
  (lt : lc t) :
  lc (subst_list xs txs t) :=
begin
  induction xs generalizing txs t,
  case list.nil { simp [lt] },
  case list.cons : _ _ ih {
    cases txs,
    case list.nil { simp [lt] },
    case list.cons {
      simp at ln_eq,
      simp at ltxs,
      simp [ih ln_eq ltxs.2 (subst_lc ltxs.1 lt)] } }
end

-- Mapping substitution over a list of types is locally-closed if all type
-- arguments are locally-closed.
theorem map_subst_lc (lt : lc t) (lts : ∀ t ∈ ts, lc t) :
  ∀ t ∈ map (subst x t) ts, lc t :=
begin
  induction ts,
  case list.nil { simp },
  case list.cons : _ _ ih {
    simp at lts,
    exact forall_mem_cons.mpr ⟨subst_lc lt lts.1, ih lts.2⟩ }
end

end /- namespace -/ typ --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
