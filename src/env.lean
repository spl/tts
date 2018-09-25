import data.finmap
import sch

namespace tts ------------------------------------------------------------------

/-- Binding type -/
abbreviation bty (V : Type) (x : tagged V) : Type :=
sch V

/-- A (non-dependent) pair of a variable and a type scheme -/
abbreviation binding (V : Type) : Type :=
sigma (bty V)

/-- Construct a binding -/
abbreviation binding.mk {V : Type} : tagged V → sch V → binding V :=
sigma.mk

/- Notation for a binding -/
infix ` :~ `:80 := binding.mk

/-- Free variables of a binding -/
abbreviation binding.fv {V : Type} [decidable_eq V] (b : binding V) : finset (tagged V) :=
sch.fv b.2

/-- Environment mapping variables to bindings -/
abbreviation env (V : Type) : Type :=
finmap (tagged V) (bty V)

/-- Domain of an environment -/
abbreviation dom {V : Type} (Γ : env V) : finset (tagged V) :=
finmap.keys Γ

end /- namespace -/ tts --------------------------------------------------------
