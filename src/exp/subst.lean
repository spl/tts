import .fv

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {x y : tagged V} -- Variable names
variables {e ex : exp V} -- Expressions

variables [decidable_eq V]

open occurs

-- Properties of subst

@[simp]
theorem subst_var_bound : subst x e (var bound y) = var bound y :=
  rfl

@[simp]
lemma subst_var_free_eq (h : x = y) : subst x e (var free y) = e :=
  by simp [subst, h]

@[simp]
lemma subst_var_free_ne (h : x ≠ y) : subst x e (var free y) = var free y :=
  by simp [subst, h]

@[simp]
lemma subst_app {ef ea : exp V} : subst x e (app ef ea) = app (subst x e ef) (subst x e ea) :=
  rfl

@[simp]
lemma subst_lam {v} {eb : exp V} : subst x e (lam v eb) = lam v (subst x e eb) :=
  rfl

@[simp]
lemma subst_let_ {v} {ed eb : exp V} : subst x e (let_ v ed eb) = let_ v (subst x e ed) (subst x e eb) :=
  rfl

@[simp]
lemma subst_fresh (h : x ∉ fv e) : subst x ex e = e :=
  by induction e with o; try {cases o}; try {simp at h}; try {cases h}; simp *

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
