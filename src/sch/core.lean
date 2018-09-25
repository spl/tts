import data.fresh
import typ.core

namespace tts ------------------------------------------------------------------

-- Grammar of type schemes.
@[derive decidable_eq]
structure sch (V : Type) : Type :=
  (arity : ℕ)
  (type : typ V)

attribute [pp_using_anonymous_constructor] sch

variables {V : Type} -- Type of variable names

namespace sch ------------------------------------------------------------------
variables [_root_.decidable_eq V]

theorem eq_of_veq : ∀ {s₁ s₂ : sch V}, s₁.arity = s₂.arity → s₁.type = s₂.type → s₁ = s₂
| ⟨a₁, t₁⟩ ⟨a₂, t₂⟩ ha ht := by congr; solve_by_elim

-- Get the free variables of a scheme.
def fv (s : sch V) : finset (tagged V) :=
  typ.fv s.type

@[simp]
theorem fv_mk {a : ℕ} {t : typ V} : fv (mk a t) = typ.fv t :=
  rfl

-- Substitute a free variable for a type in a scheme
def subst (x : tagged V) (t : typ V) (s : sch V) : sch V :=
  ⟨s.arity, typ.subst x t s.type⟩

@[simp]
theorem subst_mk {a : ℕ} {x : tagged V} {tx t : typ V} : subst x tx (mk a t) = mk a (typ.subst x tx t) :=
  rfl

-- Substitute a list of free variables for a list of types in a scheme
def subst_list (xs : list (tagged V)) (ts : list (typ V)) (s : sch V) : sch V :=
  ⟨s.arity, typ.subst_list xs ts s.type⟩

@[simp]
theorem subst_list_mk {a : ℕ} {xs : list (tagged V)} {ts : list (typ V)} {t : typ V} : subst_list xs ts (mk a t) = mk a (typ.subst_list xs ts t) :=
  rfl

-- Open a type scheme with a list of types for bound variables.
def open_typs (ts : list (typ V)) (s : sch V) : typ V :=
  typ.open_typs ts s.type

@[simp]
theorem open_typs_mk {ts : list (typ V)} {a : ℕ} {t : typ V} : open_typs ts (mk a t) = typ.open_typs ts t :=
  rfl

-- Open a type scheme with a list of free variables for bound variables.
def open_vars (xs : list (tagged V)) (s : sch V) : typ V :=
  typ.open_vars xs s.type

@[simp]
theorem open_vars_mk {xs : list (tagged V)} {a : ℕ} {t : typ V} : open_vars xs (mk a t) = typ.open_vars xs t :=
  rfl

-- A scheme is locally-closed if its body is locally closed.
def lc (s : sch V) : Prop :=
  typ.lc_body s.arity s.type

end /- namespace -/ sch --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
