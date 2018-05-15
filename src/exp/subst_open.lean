import exp.open
import .lc
import .subst

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {k i : ℕ} -- Natural numbers
variables {V : Type} -- Type of variable names
variables {x y : V} -- Variable names
variables {e ex e₁ e₂ : exp V} -- Expressions

variables [decidable_eq V] [finset.has_fresh V]

lemma subst_open.rec (lx : lc ex)
: subst x ex (open.rec e₂ k e₁) = open.rec (subst x ex e₂) k (subst x ex e₁) :=
  begin
    induction e₁ generalizing k; simp [subst, open.rec],
    case exp.varb : i {
      by_cases h : k = i,
      {/- h : k = i -/ simp [h]},
      {/- h : k ≠ i -/ simp [h, subst]}
    },
    case exp.varf : y {
      by_cases h : x = y,
      {/- h : x = y -/ simp [h, open_lc.rec lx]},
      {/- h : x ≠ y -/ simp [h, open.rec]}
    },
    case exp.app : ef ea rf ra {
      simp [rf, ra]
    },
    case exp.lam : eb rb {
      simp [rb]
    },
    case exp.let_ : ed eb rd rb {
      simp [rd, rb]
    }
  end

lemma subst_open
: lc ex → subst x ex (exp.open e₂ e₁) = exp.open (subst x ex e₂) (subst x ex e₁) :=
  subst_open.rec

lemma subst_open_var (p : x ≠ y) (lx : lc ex)
: subst x ex (open_var y e₁) = open_var y (subst x ex e₁) :=
  by simp [open_var, subst_open lx, subst_varf_of_ne p]

-- subst_intro

lemma subst_intro.rec.varb
: open.rec e k (varb i) = subst x e (open.rec (varf x) k (varb i)) :=
  begin
    repeat { rw open.rec },
    by_cases h : k = i,
    {/- h : k = i -/ repeat { rw if_pos h }, rw subst_varf},
    {/- h : k ≠ i -/ repeat { rw if_neg h }, rw subst}
  end

lemma subst_intro.rec.varf (p : x ≠ y)
: open.rec e k (varf y) = subst x e (open.rec (varf x) k (varf y)) :=
  by repeat { rw open.rec }; rw subst_varf_of_ne p

lemma subst_intro.rec
: ∀ {e₁ : exp V} (k : ℕ), x ∉ fv e₁ → open.rec e₂ k e₁ = subst x e₂ (open.rec (varf x) k e₁)
  | (varb i)     k p := exp.subst_intro.rec.varb
  | (varf y)     k p := exp.subst_intro.rec.varf (fv_not_mem_varf.mp p)
  | (app ef ea)  k p :=
    begin
      rw fv_app at p,
      simp [open.rec, subst, subst_intro.rec k p.1, subst_intro.rec k p.2]
    end
  | (lam eb)     k p :=
    begin
      rw fv_lam at p,
      simp [open.rec, subst, subst_intro.rec (k + 1) p]
    end
  | (let_ ed eb) k p :=
    begin
      rw fv_let_ at p,
      simp [open.rec, subst, subst_intro.rec k p.1, subst_intro.rec (k + 1) p.2]
    end

lemma subst_intro (p : x ∉ fv e₁) : exp.open e₂ e₁ = subst x e₂ (open_var x e₁) :=
  subst_intro.rec 0 p

-- Locally-closed expressions are stable over substitution
lemma subst_lc (x : V) (lx : lc ex) (l : lc e) : lc (subst x ex e) :=
  begin
    induction l generalizing ex lx x; simp [subst],
    case lc.varf : y {
      by_cases h : x = y,
      {/- h : x = y -/ simp [h], exact lx},
      {/- h : x ≠ y -/ simp [h]},
    },
    case lc.app : ef ea lf la rf ra {
      exact ⟨rf lx x, ra lx x⟩
    },
    case lc.lam : L eb Fb rb {
      existsi L ∪ {x},
      intros y py,
      rw finset.not_mem_union at py,
      have rb : lc (subst x ex (open_var y eb)) := rb py.1 lx x,
      have x_ne_y : x ≠ y := ne.symm (finset.not_mem_singleton.mp py.2),
      rwa subst_open_var x_ne_y lx at rb
    },
    case lc.let_ : L ed eb ld Fb rd rb {
      split,
      { exact rd lx x },
      {
        existsi L ∪ {x},
        intros y py,
        rw finset.not_mem_union at py,
        have rb : lc (subst x ex (open_var y eb)) := rb py.1 lx x,
        have x_ne_y : x ≠ y := ne.symm (finset.not_mem_singleton.mp py.2),
        rwa subst_open_var x_ne_y lx at rb
      },
    }
  end

theorem lc_open (h₁ : e₁.lc_body) (h₂ : e₂.lc) : (exp.open e₂ e₁).lc :=
  begin
    cases h₁ with L F,
    let L := fv e₁ ∪ L,
    let fr := finset.not_mem_union.mp (finset.fresh_not_mem L),
    rw subst_intro fr.1,
    exact subst_lc (finset.fresh L) h₂ (F fr.2)
  end

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
