import data.finset

@[simp] theorem nat.lt_succ_max_left (m n : ℕ) : m < max m n + 1 :=
by rw [nat.lt_succ_iff]; apply le_max_left

@[simp] theorem nat.lt_succ_max_right (m n : ℕ) : n < max m n + 1 :=
by rw [nat.lt_succ_iff]; apply le_max_right

local attribute [-simp] add_comm

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

@[simp]
def depth : exp V → ℕ
  | (varb _)     := 0
  | (varf _)     := 0
  | (app ef ea)  := max (depth ef) (depth ea) + 1
  | (lam eb)     := depth eb + 1
  | (let_ ed eb) := max (depth ed) (depth eb) + 1

@[simp]
theorem depth_app₁ {ef ea : exp V} : depth ef < depth (app ef ea) :=
  by simp [depth]

@[simp]
theorem depth_app₂ {ef ea : exp V} : depth ea < depth (app ef ea) :=
  by simp [depth]

@[simp]
theorem depth_let₁ {ed eb : exp V} : depth ed < depth (let_ ed eb) :=
  by simp [depth]

@[simp]
theorem depth_let₂ {ed eb : exp V} : depth eb < depth (let_ ed eb) :=
  by simp [depth]

instance : has_sizeof (exp V) :=
  ⟨depth⟩

-- Open an expression (last parameter) with an expression (eb) for a bound
-- variable.
protected
def open.rec (e : exp V) : ℕ → exp V → exp V
  | k (varb i)     := if k = i then e else varb i
  | k (varf x)     := varf x
  | k (app ef ea)  := app (open.rec k ef) (open.rec k ea)
  | k (lam eb)     := lam (open.rec (k + 1) eb)
  | k (let_ ed eb) := let_ (open.rec k ed) (open.rec (k + 1) eb)

@[simp]
theorem depth_open_rec_var {x k} {e : exp V}
: depth (open.rec (varf x) k e) = depth e :=
  begin
    induction e with i generalizing k,
    by_cases k = i,
    all_goals { simp [open.rec, depth, *] }
  end

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
def open_var (x : V) : exp V → exp V :=
  exp.open (varf x)

@[simp]
theorem depth_open_var_lam {x} {e : exp V}
: depth (open_var x e) = depth e :=
  by simp [open_var, exp.open, exp.open.rec]

-- Property of a locally-closed expression
inductive lc : exp V → Prop
  | varf : Π (x : V),                                                                          lc (varf x)
  | app  : Π                {ef ea : exp V}, lc ef → lc ea →                                   lc (app ef ea)
  | lam  : Π {L : finset V} {eb : exp V},            (∀ {x : V}, x ∉ L → lc (open_var x eb)) → lc (lam eb)
  | let_ : Π {L : finset V} {ed eb : exp V}, lc ed → (∀ {x : V}, x ∉ L → lc (open_var x eb)) → lc (let_ ed eb)

def lc' : exp V → Prop
  | (varb _)     := false
  | (varf _)     := true
  | (app ef ea)  := lc' ef ∧ lc' ea
  | (lam eb)     := ∃ (L : finset V), ∀ {x}, x ∉ L → lc' (open_var x eb)
  | (let_ ed eb) := lc' ed ∧ ∃ (L : finset V), ∀ {x}, x ∉ L → lc' (open_var x eb)
  using_well_founded {
    dec_tac := `[simp [measure, inv_image, nat.pos_iff_ne_zero']],
    rel_tac := λ_ _, `[exact ⟨_, measure_wf depth⟩] }

-- Locally-closed body of a lambda- or let-expression
def lc_body (eb : exp V) : Prop :=
  ∃ (L : finset V), ∀ {x : V}, x ∉ L → (open_var x eb).lc

-- Grammar of values
inductive value : exp V → Prop
  | lam  : Π {e : exp V}, e.lc_body → value (lam e)

-- Reduction rules
inductive red : exp V → exp V → Prop
  | app₁  : Π {ef ef' ea : exp V}, red ef ef' → ea.lc      → red (app ef ea)       (app ef' ea)
  | app₂  : Π {ef ea ea' : exp V}, ef.value   → red ea ea' → red (app ef ea)       (app ef ea')
  | lam   : Π {eb ea : exp V},     eb.lc_body → ea.value   → red (app (lam eb) ea) (exp.open ea eb)
  | let₁  : Π {ed ed' eb : exp V}, red ed ed' → eb.lc_body → red (let_ ed eb)      (let_ ed' eb)
  | let₂  : Π {ed eb : exp V},     ed.value   → eb.lc_body → red (let_ ed eb)      (exp.open ed eb)

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
