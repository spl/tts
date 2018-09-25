import .core

namespace tts ------------------------------------------------------------------
namespace typ ------------------------------------------------------------------
variables {V : Type} [_root_.decidable_eq V] -- Type of variable names
variables {x y : tagged V} -- Variable
variables {t t₁ t₂ : typ V} -- Types
variables {ts ts₁ ts₂ : list (typ V)} -- Lists of types

open occurs

/-- Free variables of a type -/
def fv : typ V → finset (tagged V)
| (var bound _) := ∅
| (var free x)  := {x}
| (arr t₁ t₂)   := fv t₁ ∪ fv t₂

@[simp] theorem fv_not_mem_var_free : x ∉ fv (var free y) ↔ x ≠ y :=
by simp [fv]

@[simp] theorem fv_not_mem_arr : x ∉ fv (arr t₁ t₂) ↔ x ∉ fv t₁ ∧ x ∉ fv t₂ :=
by simp [fv, not_or_distrib]

/-- Free variables of a list of types -/
def fv_list : list (typ V) → finset (tagged V)
| []        := ∅
| (t :: ts) := fv t ∪ fv_list ts

@[simp] theorem fv_list_nil : fv_list ([] : list (typ V)) = ∅ :=
rfl

@[simp] theorem fv_list_cons : fv_list (t :: ts) = fv t ∪ fv_list ts :=
rfl

@[simp] theorem fv_list_append : fv_list (ts₁ ++ ts₂) = fv_list ts₁ ∪ fv_list ts₂ :=
by induction ts₁ with _ _ ih; [simp, simp [ih]]

end /- namespace -/ typ --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
