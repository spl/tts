import .defs
import data.finset.fresh

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} -- Type of variable names

-- Properties of lc

lemma lc.app.unfold {ef ea : exp V} (l : lc (app ef ea)) : lc ef ∧ lc ea :=
  by cases l with _ _ _ l₁ l₂; exact ⟨l₁, l₂⟩

lemma lc.lam.unfold {eb : exp V} (l : lc (lam eb)) : ∃ (L : finset V), ∀ {x : V}, x ∉ L → lc (eb.open_var x) :=
  by cases l with _ _ _ _ _ L _ F; exact ⟨L, @F⟩

-- Properties of open

lemma open_lc.core {e₁ e₂ e₃ : exp V} {k₂ k₃ : ℕ} (p : k₂ ≠ k₃)
: open.rec e₂ k₂ (open.rec e₃ k₃ e₁) = open.rec e₃ k₃ e₁ → open.rec e₂ k₂ e₁ = e₁ :=
  begin
    induction e₁ generalizing e₂ e₃ k₂ k₃; repeat {rw open.rec},
    case exp.varb : i {
      by_cases h : k₃ = i,
      {/- h : k₃ = i -/ induction h, rw [if_pos (eq.refl k₃), if_neg p], intro, refl},
      {/- h : k₃ ≠ i -/ rw [if_neg h, open.rec], exact id}
    },
    case exp.varf : x {
      exact id
    },
    case exp.app : ef ea rf ra {
      intro h,
      injection h with hf ha,
      conv {to_lhs, rw [rf p hf, ra p ha]}
    },
    case exp.lam : eb rb {
      intro h,
      injection h with hb,
      conv {to_lhs, rw rb (mt nat.succ.inj p) hb}
    },
    case exp.let_ : ed eb rd rb {
      intro h,
      injection h with hd hb,
      conv {to_lhs, rw [rd p hd, rb (mt nat.succ.inj p) hb]}
    }
  end

variables [finset.has_fresh V]

lemma open_lc.rec {e₁ e₂ : exp V} {k : ℕ} (l : lc e₁) : open.rec e₂ k e₁ = e₁ :=
  begin
    induction l generalizing e₂ k; rw open.rec,
    case lc.app : ef ea lf la rf ra {
      rw [rf, ra]
    },
    case lc.lam : L eb Fb rb {
      rw open_lc.core (nat.succ_ne_zero k) (rb (finset.fresh_not_mem L))
    },
    case lc.let_ : L ed eb ld Fb rd rb {
      rw [rd, open_lc.core (nat.succ_ne_zero k) (rb (finset.fresh_not_mem L))]
    }
  end

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
