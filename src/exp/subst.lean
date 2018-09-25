import .fv

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {x y : tagged V} -- Variable names
variables {e ex : exp V} -- Expressions

variables [decidable_eq V]

open occurs

/-- Substitute a free variable for an expression in an expression -/
def subst (x : tagged V) (ex : exp V) : exp V → exp V
| (var bound y)  := var bound y
| (var free y)   := if x = y then ex else var free y
| (app ef ea)    := app (subst ef) (subst ea)
| (lam v eb)     := lam v (subst eb)
| (let_ v ed eb) := let_ v (subst ed) (subst eb)

@[simp] theorem subst_var_bound : subst x ex (var bound y) = var bound y :=
rfl

@[simp] theorem subst_var_free_eq (h : x = y) :
  subst x ex (var free y) = ex :=
by simp [subst, h]

@[simp] theorem subst_var_free_ne (h : x ≠ y) :
  subst x ex (var free y) = var free y :=
by simp [subst, h]

@[simp] theorem subst_app {ef ea : exp V} :
  subst x ex (app ef ea) = app (subst x ex ef) (subst x ex ea) :=
rfl

@[simp] theorem subst_lam {v} {eb : exp V} :
  subst x ex (lam v eb) = lam v (subst x ex eb) :=
rfl

@[simp] theorem subst_let_ {v} {ed eb : exp V} :
  subst x ex (let_ v ed eb) = let_ v (subst x ex ed) (subst x ex eb) :=
rfl

@[simp] theorem subst_fresh (h : x ∉ fv e) : subst x ex e = e :=
by induction e with o; try {cases o}; try {simp at h}; try {cases h}; simp *

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
