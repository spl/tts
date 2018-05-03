import data.finset

namespace tts ------------------------------------------------------------------

-- Grammar of expressions.
inductive exp (V : Type) : Type
  | varb {} : ℕ → exp          -- bound variable
  | varf    : V → exp          -- free variable
  | app     : exp → exp → exp  -- function application
  | lam     : exp → exp        -- lambda-abstraction
  | let_    : exp → exp → exp  -- let-abstraction

variables {V : Type} -- Type of variable names

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

variables [decidable_eq V]

-- Get the free variables of an expression
def fv : exp V → finset V
  | (varb i)     := ∅
  | (varf x)     := {x}
  | (app ef ea)  := fv ef ∪ fv ea
  | (lam eb)     := fv eb
  | (let_ ed eb) := fv ed ∪ fv eb

-- Substitute a free variable for an expression in an expression
def subst (x : V) (e : exp V) : exp V → exp V
  | (varb i)     := varb i
  | (varf y)     := if x = y then e else varf y
  | (app ef ea)  := app (subst ef) (subst ea)
  | (lam eb)     := lam (subst eb)
  | (let_ ed eb) := let_ (subst ed) (subst eb)

end /- namespace -/ exp --------------------------------------------------------

-- Open an expression with an expression (eb) for the last bound variable (0).
-- Note: This definition is defined outside the `exp` namespace because it
-- conflicts with the keyword `open` if declared without the `exp`. prefix.
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
  | varf : Π (x : V),                                                                          lc (varf x)
  | app  : Π                {ef ea : exp V}, lc ef → lc ea →                                   lc (app ef ea)
  | lam  : Π {L : finset V} {eb : exp V},            (∀ {x : V}, x ∉ L → lc (eb.open_var x)) → lc (lam eb)
  | let_ : Π {L : finset V} {ed eb : exp V}, lc ed → (∀ {x : V}, x ∉ L → lc (eb.open_var x)) → lc (let_ ed eb)

def lc_body (eb : exp V) : Prop :=
  ∃ (L : finset V), ∀ {x : V}, x ∉ L → (eb.open_var x).lc

-- Grammar of values
inductive value : exp V → Prop
  | lam  : Π {e : exp V}, (lam e).lc → value (lam e)

-- Reduction rules
inductive red : exp V → exp V → Prop
  | app₁  : Π {e₁ e₁' e₂ : exp V}, red e₁ e₁' →  e₂.lc →           red (app e₁ e₂)       (app e₁' e₂)
  | app₂  : Π {e₁ e₂ e₂' : exp V}, e₁.value →    red e₂ e₂' →      red (app e₁ e₂)       (app e₁ e₂')
  | lam   : Π {e₁ e₂ : exp V},     (lam e₁).lc → e₂.value →        red (app (lam e₁) e₂) (e₁.open e₂)
  | let₁  : Π {e₁ e₁' e₂ : exp V}, red e₁ e₁' →  e₂.lc_body →      red (let_ e₁ e₂)      (let_ e₁' e₂)
  | let₂  : Π {e₁ e₂ : exp V},     e₁.value →    (let_ e₁ e₂).lc → red (let_ e₁ e₂)      (e₂.open e₁)

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
