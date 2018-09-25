import exp.open
import .lc
import .subst

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {k i : ℕ} -- Natural numbers
variables {V : Type} -- Type of variable names
variables {x y : tagged V} -- Variable names
variables {e ex e₁ e₂ : exp V} -- Expressions

variables [decidable_eq V]

open occurs

@[simp]
lemma subst_open_exp (lx : lc ex)
: subst x ex (open_exp e₂ k e₁) = open_exp (subst x ex e₂) k (subst x ex e₁) :=
  begin
    induction e₁ generalizing k,
    case exp.var : o y {
      cases o,
      { by_cases h : k = y.tag; simp [h] },
      { by_cases h : x = y; simp [h, open_exp_of_lc lx] }
    },
    case exp.app : ef ea rf ra {
      simp [rf, ra]
    },
    case exp.lam : v eb rb {
      simp [rb]
    },
    case exp.let_ : v ed eb rd rb {
      simp [rd, rb]
    }
  end

@[simp]
lemma subst_open_exp₀
: lc ex → subst x ex (open_exp₀ e₂ e₁) = open_exp₀ (subst x ex e₂) (subst x ex e₁) :=
  subst_open_exp

@[simp]
lemma subst_open_var (lx : lc ex) (h : x ≠ y)
: subst x ex (open_var y e₁) = open_var y (subst x ex e₁) :=
  by simp [open_var, h, lx]

@[simp]
lemma subst_open_fresh {v} {L : finset (tagged V)} (lx : lc ex)
(h : (fresh.tagged v).gen L ≠ x)
: subst x ex (open_fresh v L e₁) = open_fresh v L (subst x ex e₁) :=
  subst_open_var lx (ne.symm h)

-- subst_intro

lemma subst_intro
: ∀ {e₁ : exp V} k, x ∉ fv e₁ → open_exp e₂ k e₁ = subst x e₂ (open_exp (var free x) k e₁)
  | (var bound y)  k p := by by_cases h : k = y.tag; simp [h]
  | (var free y)   k p := by simp at p; simp [p]
  | (app ef ea)    k p := by simp at p; simp [subst_intro k p.1, subst_intro k p.2]
  | (lam v eb)     k p := by simp at p; simp [subst_intro (k + 1) p]
  | (let_ v ed eb) k p := by simp at p; simp [subst_intro k p.1, subst_intro (k + 1) p.2]

lemma subst_intro₀ : x ∉ fv e₁ → open_exp₀ e₂ e₁ = subst x e₂ (open_var x e₁) :=
  subst_intro 0

-- Locally-closed expressions are stable over substitution
lemma subst_lc (x : tagged V) (lx : lc ex) (l : lc e) : lc (subst x ex e) :=
  begin
    induction l generalizing ex lx x,
    case lc.var : y {
      by_cases h : x = y; simp [h, lx]
    },
    case lc.app : ef ea lf la rf ra {
      exact lc.app (rf lx x) (ra lx x)
    },
    case lc.lam : v L eb lb rb {
      apply lc.lam (L ∪ {x}),
      intros y Fy,
      simp [not_or_distrib] at Fy,
      rw ←subst_open_var lx (ne.symm Fy.2),
      exact rb Fy.1 lx x
    },
    case lc.let_ : v L ed eb ld lb rd rb {
      apply lc.let_ (L ∪ {x}) (rd lx x),
      intros y Fy,
      simp [not_or_distrib] at Fy,
      rw ←subst_open_var lx (ne.symm Fy.2),
      exact rb Fy.1 lx x
    }
  end

theorem lc_open (v : V) (lb : lc_body e₁) (l₂ : lc e₂) : lc (open_exp₀ e₂ e₁) :=
  begin
    cases lb with L l₁,
    have F : (fresh.tagged v).gen (L ∪ fv e₁) ∉ L ∧ (fresh.tagged v).gen (L ∪ fv e₁) ∉ fv e₁ :=
      (fresh.tagged v).gen_not_mem_union _ _,
    rw subst_intro₀ F.2,
    exact subst_lc _ l₂ (l₁ F.1)
  end

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
