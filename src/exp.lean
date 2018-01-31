import data.finset

namespace tts ------------------------------------------------------------------
variables {V : Type} -- Type of variable names

-- Grammar of expressions
inductive exp (V : Type) : Type
  | bvar {} : ℕ → exp          -- bound variable
  | fvar    : V → exp          -- free variable
  | app     : exp → exp → exp  -- function application
  | lam     : exp → exp        -- lambda-abstraction
  | let_    : exp → exp → exp  -- let-abstraction

namespace exp ------------------------------------------------------------------

-- Open an expression with an expression for a bound variable
def open_for : ℕ → exp V → exp V → exp V
  | k eb (bvar i)     := if k = i then eb else bvar i
  | k eb (fvar x)     := fvar x
  | k eb (app e₁ e₂)  := app (open_for k eb e₁) (open_for k eb e₂)
  | k eb (lam e)      := lam (open_for (k+1) eb e)
  | k eb (let_ e₁ e₂) := let_ (open_for k eb e₁) (open_for (k+1) eb e₂)

end /- namespace -/ exp --------------------------------------------------------

-- Open an expression with an expression for the last bound variable
protected
def exp.open : exp V → exp V → exp V :=
  exp.open_for 0

-- Open an expression with a free variable for the last bound variable
protected
def exp.open_var (x : V) : exp V → exp V :=
  exp.open (exp.fvar x)

namespace exp ------------------------------------------------------------------

-- Property of a locally-closed expression
inductive lc : exp V → Prop
  | fvar : Π (x : V),                                                                        lc (fvar x)
  | app  : Π            {e₁ e₂ : exp V},     lc e₁ → lc e₂ →                                 lc (app e₁ e₂)
  | lam  : Π {L : finset V} {e : exp V},             (∀ x : V, x ∉ L → lc (e.open_var x)) →  lc (lam e)
  | let_ : Π {L : finset V} {e₁ e₂ : exp V}, lc e₁ → (∀ x : V, x ∉ L → lc (e₂.open_var x)) → lc (let_ e₁ e₂)

/-
Definition term_body t :=
  exists L, forall x, x ∉ L -> term (t ^ x).
-/

def lc_body (e : exp V) : Prop :=
  ∃ L : finset V, ∀ x : V, x ∉ L → lc (e.open_var x)

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
