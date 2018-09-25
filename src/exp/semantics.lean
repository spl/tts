import tactics .subst_open

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables [decidable_eq V]
variables {e₁ e₂ : exp V} -- Expressions

/-- Grammar of values -/
inductive value : exp V → Prop
| lam : Π {v} {e : exp V}, lc_body e → value (lam v e)

theorem lc_of_value : ∀ {e : exp V}, value e → lc e
| _ (value.lam p) := lc_lam.mpr p

/-- Reduction rules -/
inductive red : exp V → exp V → Prop
| app₁  : Π {ef ef' ea : exp V},     red ef ef' → ea.lc      → red (app ef ea)         (app ef' ea)
| app₂  : Π {ef ea ea' : exp V},     value ef   → red ea ea' → red (app ef ea)         (app ef ea')
| lam   : Π {v} {eb ea : exp V},     lc_body eb → value ea   → red (app (lam v eb) ea) (open_exp₀ ea eb)
| let₁  : Π {v} {ed ed' eb : exp V}, red ed ed' → lc_body eb → red (let_ v ed eb)      (let_ v ed' eb)
| let₂  : Π {v} {ed eb : exp V},     value ed   → lc_body eb → red (let_ v ed eb)      (open_exp₀ ed eb)

theorem lc_of_red_left (h : red e₁ e₂) : lc e₁ :=
by induction h; simp [and.assoc] at *; note_all_applied lc_of_value; tauto

theorem lc_of_red_right (h : red e₁ e₂) : lc e₂ :=
begin
  induction h,
  case red.app₁ { simp at *, tauto },
  case red.app₂ { simp at *, note_all_applied lc_of_value, tauto },
  case red.lam : v _ _ lc_eb val_ea { exact lc_open_exp₀ v lc_eb (lc_of_value val_ea) },
  case red.let₁ { simp at *, tauto },
  case red.let₂ : v _ _ val_ed lc_eb { exact lc_open_exp₀ v lc_eb (lc_of_value val_ed) }
end

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
