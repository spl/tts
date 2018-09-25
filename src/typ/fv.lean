import .core

namespace tts ------------------------------------------------------------------
namespace typ ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {x x₁ x₂ : tagged V} -- Variable
variables {t t₁ t₂ : typ V} -- Types
variables {ts ts₁ ts₂ : list (typ V)} -- Lists of types

variables [_root_.decidable_eq V]

open occurs

@[simp]
theorem fv_not_mem_var_free : x₁ ∉ fv (var free x₂) ↔ x₁ ≠ x₂ :=
  by simp [fv]

@[simp]
theorem fv_not_mem_arr : x ∉ fv (arr t₁ t₂) ↔ x ∉ fv t₁ ∧ x ∉ fv t₂ :=
  by simp [fv, decidable.not_or_iff_and_not]

@[simp]
theorem fv_list_nil : fv_list ([] : list (typ V)) = ∅ :=
  rfl

@[simp]
theorem fv_list_cons : fv_list (t :: ts) = fv t ∪ fv_list ts :=
  rfl

@[simp]
theorem fv_list_append : fv_list (ts₁ ++ ts₂) = fv_list ts₁ ∪ fv_list ts₂ :=
  by induction ts₁ with _ _ ih; [simp, simp [ih]]

end /- namespace -/ typ --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
