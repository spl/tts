import .fv

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {x y : V} -- Variable names
variables {e e₁ e₂ : exp V} -- Expressions

variables [decidable_eq V]

-- Properties of subst

lemma subst_varf : subst x e (varf x) = e :=
  by rw subst; rw if_pos (eq.refl x)

lemma subst_varf_of_ne (p : x ≠ y) : subst x e (varf y) = varf y :=
  by rw subst; rw if_neg p

lemma subst_varf_of_not_mem (p : x ∉ finset.singleton y) : subst x e (varf y) = varf y :=
  by rw subst; rw if_neg (finset.not_mem_singleton.mp p)

lemma subst_fresh (p : x ∉ fv e₁) : subst x e₂ e₁ = e₁ :=
  begin
    induction e₁ generalizing p; repeat { rw subst },
    case exp.varf : y           { exact subst_varf_of_not_mem p        },
    case exp.app  : ef ea rf ra { rw fv_app at p, rw [rf p.1, ra p.2]  },
    case exp.lam  : eb rb       { rw fv_lam at p, rw rb p              },
    case exp.let_ : ed eb rd rb { rw fv_let_ at p, rw [rd p.1, rb p.2] }
  end

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
