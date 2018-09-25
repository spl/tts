import typ

namespace tts ------------------------------------------------------------------

/-- Grammar of type schemes -/
@[derive decidable_eq]
structure sch (V : Type) : Type :=
(arity : ℕ)
(type : typ V)

attribute [pp_using_anonymous_constructor] sch

namespace sch ------------------------------------------------------------------
variables {V : Type} [_root_.decidable_eq V] -- Type of variable names
variables {a : ℕ} -- Type scheme arity
variables {x : tagged V} -- Variables
variables {xs : list (tagged V)} -- List of variables
variables {t tx : typ V} -- Types
variables {ts txs : list (typ V)} -- Lists of types

theorem eq_of_veq : ∀ {s₁ s₂ : sch V}, s₁.arity = s₂.arity → s₁.type = s₂.type → s₁ = s₂
| ⟨a₁, t₁⟩ ⟨a₂, t₂⟩ ha ht := by congr; solve_by_elim

/-- Get the free variables of a scheme -/
def fv (s : sch V) : finset (tagged V) :=
typ.fv s.type

@[simp] theorem fv_mk : fv (mk a t) = typ.fv t :=
rfl

/-- Open a type scheme with a list of types for bound variables -/
def open_typs (ts : list (typ V)) (s : sch V) : typ V :=
typ.open_typs ts s.type

@[simp] theorem open_typs_mk : open_typs ts (mk a t) = typ.open_typs ts t :=
rfl

/-- Open a type scheme with a list of free variables for bound variables -/
def open_vars (xs : list (tagged V)) (s : sch V) : typ V :=
typ.open_vars xs s.type

@[simp] theorem open_vars_mk : open_vars xs (mk a t) = typ.open_vars xs t :=
rfl

/-- Locally-closed type scheme -/
def lc (s : sch V) : Prop :=
typ.lc_body s.arity s.type

end /- namespace -/ sch --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
