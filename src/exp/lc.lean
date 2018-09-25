import exp.open

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} [decidable_eq V] -- Type of variable names
variables {k k₂ k₃ : ℕ} -- Natural numbers
variables {v : V} -- Variable names
variables {x : tagged V} -- Variables
variables {e ea eb ed ef e₁ e₂ e₃ : exp V} -- Expressions

open occurs

/-- Locally-close expression -/
inductive lc : exp V → Prop
| var  : Π x,                                                                                                    lc (var free x)
| app  : Π                {ef ea : exp V},              lc ef → lc ea →                                          lc (app ef ea)
| lam  : Π {v} (L : finset (tagged V)) {eb : exp V},            (∀ {x : tagged V}, x ∉ L → lc (open_var x eb)) → lc (lam v eb)
| let_ : Π {v} (L : finset (tagged V)) {ed eb : exp V}, lc ed → (∀ {x : tagged V}, x ∉ L → lc (open_var x eb)) → lc (let_ v ed eb)

/-- Locally-closed body of a lambda- or let-expression -/
def lc_body (e : exp V) : Prop :=
∃ (L : finset (tagged V)), ∀ {x : tagged V}, x ∉ L → lc (open_var x e)

@[simp] theorem lc_var (x : tagged V) : lc (var free x) :=
lc.var x

@[simp] theorem lc_app : lc (app ef ea) ↔ lc ef ∧ lc ea :=
⟨λ l, by cases l with _ _ _ l₁ l₂; exact ⟨l₁, l₂⟩, λ ⟨l₁, l₂⟩, lc.app l₁ l₂⟩

@[simp] theorem lc_lam : lc (lam v eb) ↔ lc_body eb :=
⟨λ l, by cases l; apply exists.intro; assumption; assumption,
 λ l, by cases l; apply lc.lam; assumption; assumption⟩

@[simp] theorem lc_let_ : lc (let_ v ed eb) ↔ lc ed ∧ lc_body eb :=
⟨λ l, by cases l; exact ⟨by assumption, ⟨by assumption, by assumption⟩⟩,
 by rintro ⟨_, _, _⟩; apply lc.let_; repeat {assumption}⟩

theorem open_exp_of_lc_aux (p : k₂ ≠ k₃) :
  open_exp e₂ k₂ (open_exp e₃ k₃ e₁) = open_exp e₃ k₃ e₁ → open_exp e₂ k₂ e₁ = e₁ :=
begin
  induction e₁ generalizing e₂ e₃ k₂ k₃; repeat {rw open_exp},
  case exp.var : o x {
    cases o,
    case occurs.bound {
      cases x with _ i,
      by_cases h : k₃ = i,
      { induction h, simp [p] },
      { simp [h] } },
    case occurs.free { exact id }, },
  case exp.app : ef ea ihf iha {
    intro h,
    injection h with hf ha,
    conv {to_lhs, rw [ihf p hf, iha p ha]} },
  case exp.lam : v eb rb {
    intro h,
    injection h with _ hb,
    conv {to_lhs, rw rb (mt nat.succ.inj p) hb} },
  case exp.let_ : v ed eb rd rb {
    intro h,
    injection h with _ hd hb,
    conv {to_lhs, rw [rd p hd, rb (mt nat.succ.inj p) hb]} }
end

@[simp] theorem open_exp_id (l : lc e₁) : open_exp e₂ k e₁ = e₁ :=
begin
  induction l generalizing e₂ k; rw open_exp,
  case lc.app : ef ea lf la rf ra { rw [rf, ra] },
  case lc.lam : v L eb lb rb {
    rw open_exp_of_lc_aux k.succ_ne_zero (rb ((fresh.tagged v).gen_not_mem L)) },
  case lc.let_ : v L ed eb ld Fb rd rb {
    rw [rd, open_exp_of_lc_aux k.succ_ne_zero (rb ((fresh.tagged v).gen_not_mem L))] }
end


end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
