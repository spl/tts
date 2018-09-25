import .core

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} [decidable_eq V] -- Type of variable names
variables {k k₂ k₃ : ℕ} -- Natural numbers
variables {v : V} -- Variable names
variables {x : tagged V} -- Variables
variables {e ea eb ed ef e₁ e₂ e₃ : exp V} -- Expressions

open occurs

/-- Open an expression (last parameter) with an expression (e) for a bound
variable. -/
def open_exp (e : exp V) : ℕ → exp V → exp V
| k (var bound x)  := if k = x.tag then e else var bound x
| _ (var free x)   := var free x
| k (app ef ea)    := app (open_exp k ef) (open_exp k ea)
| k (lam v eb)     := lam v (open_exp k.succ eb)
| k (let_ v ed eb) := let_ v (open_exp k ed) (open_exp k.succ eb)

@[simp] theorem open_exp_var_bound_eq (h : k = x.tag) :
  open_exp e k (var bound x) = e :=
by simp [open_exp, h]

@[simp] theorem open_exp_var_bound_ne (h : k ≠ x.tag) :
  open_exp e k (var bound x) = var bound x :=
by simp [open_exp, h]

@[simp] theorem open_exp_var_free :
  open_exp e k (var free x) = var free x :=
rfl

@[simp] theorem open_exp_app :
  open_exp e k (app ef ea) = app (open_exp e k ef) (open_exp e k ea) :=
rfl

@[simp] theorem open_exp_lam :
  open_exp e k (lam v eb) = lam v (open_exp e k.succ eb) :=
rfl

@[simp] theorem open_exp_let_ :
  open_exp e k (let_ v ed eb) = let_ v (open_exp e k ed) (open_exp e k.succ eb) :=
rfl

/-- Open an expression with an expression `e` for the last bound variable (0) -/
def open_exp₀ (e : exp V) : exp V → exp V :=
open_exp e 0

/-- Open an expression with a free variable `x` for the last bound variable -/
def open_var (x : tagged V) : exp V → exp V :=
open_exp₀ (var free x)

/-- Open an expression with a variable of the name `v` fresh from the variable
set `L` for the last bound variable. -/
def open_fresh (v : V) (L : finset (tagged V)) : exp V → exp V :=
open_var $ (fresh.tagged v).gen L

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
