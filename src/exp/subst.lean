import .fv

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} [decidable_eq V] -- Type of variable names

-- Properties of subst

lemma subst.varf.eq {x : V} {e : exp V} : subst x e (varf x) = e :=
  by rw subst; rw if_pos (eq.refl x)

lemma subst.varf.ne {x y : V} {e : exp V} (p : x ≠ y)
: subst x e (varf y) = varf y :=
  by rw subst; rw if_neg p

lemma subst.varf.not_mem {x y : V} {e : exp V} (p : x ∉ finset.singleton y)
: subst x e (varf y) = varf y :=
  by rw subst; rw if_neg (finset.not_mem_singleton.mp p)

lemma subst_fresh {x : V} {e₁ e₂ : exp V} (p : x ∉ fv e₁)
: subst x e₂ e₁ = e₁ :=
  begin
    induction e₁ generalizing p,
    case exp.varb {
      rw subst
    },
    case exp.varf : y {
      exact subst.varf.not_mem p
    },
    case exp.app : ef ea rf ra {
      repeat {rw subst},
      rw fv.app at p,
      rw [rf p.1, ra p.2]
    },
    case exp.lam : eb rb {
      rw subst,
      rw fv.lam at p,
      rw rb p
    },
    case exp.let_ : ed eb rd rb {
      repeat {rw subst},
      have p : x ∉ fv ed ∧ x ∉ fv eb := fv.let_.mp p,
      rw [rd p.1, rb p.2]
    }
  end

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
