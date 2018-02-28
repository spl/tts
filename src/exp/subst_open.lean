import exp.open
import .subst

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} [decidable_eq V] [finset.has_fresh V] -- Type of variable names

lemma subst_open.rec {x : V} {k : ℕ} {ex e₁ e₂ : exp V} (lx : lc ex)
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

lemma subst_open {x : V} {ex e₁ e₂ : exp V}
: lc ex → subst x ex (exp.open e₂ e₁) = exp.open (subst x ex e₂) (subst x ex e₁) :=
  subst_open.rec

lemma subst_open_var {x y : V} {ex e₁ : exp V} (p : x ≠ y) (lx : lc ex)
: subst x ex (exp.open_var y e₁) = exp.open_var y (subst x ex e₁) :=
  by simp [exp.open_var, subst_open lx, subst.varf.ne p]

-- subst_intro

lemma subst_intro.rec.varb {x : V} {k i : ℕ} {e : exp V}
: open.rec e k (varb i) = subst x e (open.rec (varf x) k (varb i)) :=
  begin
    repeat {rw open.rec},
    by_cases h : k = i,
    {/- h : k = i -/ repeat {rw if_pos h}, rw subst.varf.eq},
    {/- h : k ≠ i -/ repeat {rw if_neg h}, rw subst}
  end

lemma subst_intro.rec.varf {x y : V} {k : ℕ} {e : exp V} (p : x ≠ y)
: open.rec e k (varf y) = subst x e (open.rec (varf x) k (varf y)) :=
  by repeat {rw open.rec}; rw subst.varf.ne p

lemma subst_intro.rec {x : V} {e₂ : exp V}
: ∀ (k : ℕ) (e₁ : exp V), x ∉ fv e₁ → open.rec e₂ k e₁ = subst x e₂ (open.rec (varf x) k e₁)
  | k (varb i)     p := exp.subst_intro.rec.varb
  | k (varf y)     p := exp.subst_intro.rec.varf (fv.not_mem_varf.mp p)
  | k (app ef ea)  p :=
    begin
      rw fv.app at p,
      simp [open.rec, subst, subst_intro.rec k ef p.1, subst_intro.rec k ea p.2]
    end
  | k (lam eb)     p :=
    begin
      simp [open.rec, subst, subst_intro.rec (k + 1) eb p]
    end
  | k (let_ ed eb) p :=
    begin
      rw fv.let_ at p,
      simp [open.rec, subst, subst_intro.rec k ed p.1, subst_intro.rec (k + 1) eb p.2]
    end

lemma subst_intro (x : V) (e₁ e₂ : exp V) (p : x ∉ fv e₁)
: exp.open e₂ e₁ = subst x e₂ (exp.open_var x e₁) :=
  subst_intro.rec 0 e₁ p

-- Locally-closed expressions are stable over substitution
lemma subst_lc {e ex : exp V} (x : V) (lx : lc ex) (l : lc e) : lc (subst x ex e) :=
  begin
    induction l generalizing ex lx x; simp [subst],
    case lc.varf : y {
      by_cases h : x = y,
      {/- h : x = y -/ simp [h], exact lx},
      {/- h : x ≠ y -/ simp [h], exact lc.varf y},
    },
    case lc.app : ef ea lf la rf ra {
      exact lc.app (rf lx x) (ra lx x)
    },
    case lc.lam : L eb Fb rb {
      refine lc.lam (λ (y : V) (py : y ∉ L ∪ {x}), _),
      rw finset.not_mem_union at py,
      have rb : lc (subst x ex (exp.open_var y eb)) := rb py.1 lx x,
      have x_ne_y : x ≠ y := ne.symm (finset.not_mem_singleton.mp py.2),
      rwa subst_open_var x_ne_y lx at rb
    },
    case lc.let_ : L ed eb ld Fb rd rb {
      refine lc.let_ (rd lx x) (λ (y : V) (py : y ∉ L ∪ {x}), _),
      rw finset.not_mem_union at py,
      have rb : lc (subst x ex (exp.open_var y eb)) := rb py.1 lx x,
      have x_ne_y : x ≠ y := ne.symm (finset.not_mem_singleton.mp py.2),
      rwa subst_open_var x_ne_y lx at rb
    }
  end

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
