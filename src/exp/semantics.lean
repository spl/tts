import .lc
import .subst_open
import tactics

namespace tts ------------------------------------------------------------------
namespace exp ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {e₁ e₂ : exp V} -- Expressions

theorem lc_of_value : ∀ {e : exp V}, e.value → e.lc
  | _ (value.lam p) := lc_lam.mpr p

theorem lc_of_red_left (h : red e₁ e₂) : e₁.lc :=
  by induction h; simp [and.assoc] at *; note_all_applied lc_of_value; tauto

variables [decidable_eq V] [finset.has_fresh V]

theorem lc_of_red_right (h : red e₁ e₂) : e₂.lc :=
  begin
    induction h,
    case red.app₁ { simp at *, tauto },
    case red.app₂ { simp at *, note_all_applied lc_of_value, tauto },
    case red.lam : _ _ lc_eb val_ea { exact lc_open lc_eb (lc_of_value val_ea) },
    case red.let₁ { simp at *, tauto },
    case red.let₂ : _ _ val_ed lc_eb { exact lc_open lc_eb (lc_of_value val_ed) }
  end

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
