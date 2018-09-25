import .lc

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} -- Type of variable names

open occurs

-- Properties of open

lemma open_lc.core {e₁ e₂ e₃ : exp V} {k₂ k₃ : ℕ} (p : k₂ ≠ k₃)
: open_exp e₂ k₂ (open_exp e₃ k₃ e₁) = open_exp e₃ k₃ e₁ → open_exp e₂ k₂ e₁ = e₁ :=
  begin
    induction e₁ generalizing e₂ e₃ k₂ k₃; repeat {rw open_exp},
    case exp.var : o x {
      cases o,
      case occurs.bound {
        cases x with _ i,
        by_cases h : k₃ = i,
        { induction h, simp [p] },
        { simp [h] }
      },
      case occurs.free { exact id },
    },
    case exp.app : ef ea ihf iha {
      intro h,
      injection h with hf ha,
      conv {to_lhs, rw [ihf p hf, iha p ha]}
    },
    case exp.lam : v eb rb {
      intro h,
      injection h with _ hb,
      conv {to_lhs, rw rb (mt nat.succ.inj p) hb}
    },
    case exp.let_ : v ed eb rd rb {
      intro h,
      injection h with _ hd hb,
      conv {to_lhs, rw [rd p hd, rb (mt nat.succ.inj p) hb]}
    }
  end

variables [decidable_eq V]

@[simp]
lemma open_exp_of_lc {e₁ e₂ : exp V} {k : ℕ} (l : lc e₁) : open_exp e₂ k e₁ = e₁ :=
  begin
    induction l generalizing e₂ k; rw open_exp,
    case lc.app : ef ea lf la rf ra {
      rw [rf, ra]
    },
    case lc.lam : v L eb lb rb {
      rw open_lc.core k.succ_ne_zero (rb ((fresh.tagged v).gen_not_mem L))
    },
    case lc.let_ : v L ed eb ld Fb rd rb {
      rw [rd, open_lc.core k.succ_ne_zero (rb ((fresh.tagged v).gen_not_mem L))]
    }
  end

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
