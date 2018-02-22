import .type
import data.finset.extra

variables {V : Type} -- Type of variable names

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------

-- Open an expression (last parameter) with an expression (eb) for a bound
-- variable.
protected
def open.rec (e : exp V) : ℕ → exp V → exp V
  | k (varb i)     := if k = i then e else varb i
  | k (varf x)     := varf x
  | k (app ef ea)  := app (open.rec k ef) (open.rec k ea)
  | k (lam eb)     := lam (open.rec (k + 1) eb)
  | k (let_ ed eb) := let_ (open.rec k ed) (open.rec (k + 1) eb)

end /- namespace -/ exp --------------------------------------------------------

-- Open an expression with an expression (eb) for the last bound variable (0).
protected
def exp.open (eb : exp V) : exp V → exp V :=
  exp.open.rec eb 0

namespace exp ------------------------------------------------------------------

-- Open an expression with a free variable (x) for the last bound variable (0).
protected
def open_var (x : V) : exp V → exp V :=
  exp.open (varf x)

-- Property of a locally-closed expression
inductive lc : exp V → Prop
  | varf : Π (x : V),                                                                        lc (varf x)
  | app  : Π            {ef ea : exp V},     lc ef → lc ea →                                 lc (app ef ea)
  | lam  : Π {L : finset V} {eb : exp V},            (∀ x : V, x ∉ L → lc (eb.open_var x)) → lc (lam eb)
  | let_ : Π {L : finset V} {ed eb : exp V}, lc ed → (∀ x : V, x ∉ L → lc (eb.open_var x)) → lc (let_ ed eb)

def lc_body (eb : exp V) : Prop :=
  ∃ L : finset V, ∀ x : V, x ∉ L → lc (eb.open_var x)

-- Properties of lc

lemma lc.app.unfold {ef ea : exp V} (l : lc (app ef ea)) : lc ef ∧ lc ea :=
  by cases l with _ _ _ l₁ l₂; exact ⟨l₁, l₂⟩

lemma lc.lam.unfold {eb : exp V} (l : lc (lam eb)) : ∃ (L : finset V), ∀ (x : V), x ∉ L → lc (eb.open_var x) :=
  by cases l with _ _ _ _ _ L _ F; exact ⟨L, F⟩

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
      cases finset.fresh L with x px,
      rw open_lc.core (nat.succ_ne_zero k) (rb x px)
    },
    case lc.let_ : L ed eb ld Fb rd rb {
      cases finset.fresh L with x px,
      rw [rd, open_lc.core (nat.succ_ne_zero k) (rb x px)]
    }
  end

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
