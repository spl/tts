import data.fresh
import data.finset
import occurs

namespace tts ------------------------------------------------------------------

open occurs

-- Grammar of expressions.
inductive exp (V : Type) : Type
  | var  : occurs → tagged V → exp -- variable, bound or free
  | app  : exp → exp → exp         -- function application
  | lam  : V → exp → exp           -- lambda-abstraction
  | let_ : V → exp → exp → exp     -- let-abstraction

variables {V : Type} -- Type of variable names

namespace exp ------------------------------------------------------------------

protected
def repr [has_repr V] : exp V → string
  | (var bound x)  := _root_.repr x.tag ++ "⟨" ++ _root_.repr x.val ++ "⟩"
  | (var free x)   := _root_.repr x
  | (app ef ea)    := "(" ++ ef.repr ++ ") (" ++ ea.repr ++ ")"
  | (lam v eb)     := "λ " ++ _root_.repr v ++ " . " ++ eb.repr
  | (let_ v ed eb) := "let " ++ _root_.repr v ++ " = " ++ ed.repr ++ " in " ++ eb.repr

instance [has_repr V] : has_repr (exp V) :=
⟨exp.repr⟩

-- Open an expression (last parameter) with an expression (e) for a bound
-- variable.
def open_exp (e : exp V) : ℕ → exp V → exp V
  | k (var bound x)  := if k = x.tag then e else var bound x
  | _ (var free x)   := var free x
  | k (app ef ea)    := app (open_exp k ef) (open_exp k ea)
  | k (lam v eb)     := lam v (open_exp k.succ eb)
  | k (let_ v ed eb) := let_ v (open_exp k ed) (open_exp k.succ eb)

@[simp]
theorem open_exp_var_bound_eq {k} {x : tagged V} {e : exp V} (h : k = x.tag)
: open_exp e k (var bound x) = e :=
  by simp [open_exp, h]

@[simp]
theorem open_exp_var_bound_ne {k} {x : tagged V} {e : exp V} (h : k ≠ x.tag)
: open_exp e k (var bound x) = var bound x :=
  by simp [open_exp, h]

@[simp]
theorem open_exp_var_free {k} {x : tagged V} {e : exp V}
: open_exp e k (var free x) = var free x :=
  rfl

@[simp]
theorem open_exp_app {k} {e ef ea : exp V}
: open_exp e k (app ef ea) = app (open_exp e k ef) (open_exp e k ea) :=
  rfl

@[simp]
theorem open_exp_lam {k v} {e eb : exp V}
: open_exp e k (lam v eb) = lam v (open_exp e k.succ eb) :=
  rfl

@[simp]
theorem open_exp_let_ {k v} {e ed eb : exp V}
: open_exp e k (let_ v ed eb) = let_ v (open_exp e k ed) (open_exp e k.succ eb) :=
  rfl

-- Open an expression with an expression `e` for the last bound variable (0).
def open_exp₀ (e : exp V) : exp V → exp V :=
  open_exp e 0

-- Open an expression with a free variable `x` for the last bound variable.
def open_var (x : tagged V) : exp V → exp V :=
  open_exp₀ (var free x)

variables [decidable_eq V]

-- Open an expression with a variable of the name `v` fresh from the variable
-- set `L` for the last bound variable.
def open_fresh (v : V) (L : finset (tagged V)) : exp V → exp V :=
  open_var $ (fresh.tagged v).gen L

-- Get the free variables of an expression
def fv : exp V → finset (tagged V)
  | (var bound _)  := ∅
  | (var free x)   := {x}
  | (app ef ea)    := fv ef ∪ fv ea
  | (lam _ eb)     := fv eb
  | (let_ _ ed eb) := fv ed ∪ fv eb

-- Substitute a free variable for an expression in an expression
def subst (x : tagged V) (e : exp V) : exp V → exp V
  | (var bound y)  := var bound y
  | (var free y)   := if x = y then e else var free y
  | (app ef ea)    := app (subst ef) (subst ea)
  | (lam v eb)     := lam v (subst eb)
  | (let_ v ed eb) := let_ v (subst ed) (subst eb)

end /- namespace -/ exp --------------------------------------------------------

namespace exp ------------------------------------------------------------------
variables [decidable_eq V]

inductive lc : exp V → Prop
  | var  : Π x,                                                                                                    lc (var free x)
  | app  : Π                {ef ea : exp V},              lc ef → lc ea →                                          lc (app ef ea)
  | lam  : Π {v} (L : finset (tagged V)) {eb : exp V},            (∀ {x : tagged V}, x ∉ L → lc (open_var x eb)) → lc (lam v eb)
  | let_ : Π {v} (L : finset (tagged V)) {ed eb : exp V}, lc ed → (∀ {x : tagged V}, x ∉ L → lc (open_var x eb)) → lc (let_ v ed eb)

-- Locally-closed body of a lambda- or let-expression
def lc_body (e : exp V) : Prop :=
  ∃ (L : finset (tagged V)), ∀ {x : tagged V}, x ∉ L → lc (open_var x e)

-- Grammar of values
inductive value : exp V → Prop
  | lam : Π {v} {e : exp V}, lc_body e → value (lam v e)

-- Reduction rules
inductive red : exp V → exp V → Prop
  | app₁  : Π {ef ef' ea : exp V},         red ef ef' → ea.lc      → red (app ef ea)         (app ef' ea)
  | app₂  : Π {ef ea ea' : exp V},         value ef   → red ea ea' → red (app ef ea)         (app ef ea')
  | lam   : Π {v : V} {eb ea : exp V},     lc_body eb → value ea   → red (app (lam v eb) ea) (open_exp₀ ea eb)
  | let₁  : Π {v : V} {ed ed' eb : exp V}, red ed ed' → lc_body eb → red (let_ v ed eb)      (let_ v ed' eb)
  | let₂  : Π {v : V} {ed eb : exp V},     value ed   → lc_body eb → red (let_ v ed eb)      (open_exp₀ ed eb)

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
