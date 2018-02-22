import .env
import .exp

namespace tts ------------------------------------------------------------------
variables {V : Type} [decidable_eq V] -- Type of variable names

open exp
open typ

inductive typing : env V → exp V → typ V → Prop
  | varf : Π {Γ : env V} {x : V} {s : sch V} {ts : list (typ V)}
    , Γ.uniq
    → x :~ s ∈ Γ
    → lc_types s.arity ts
    → s.well_formed
    → typing Γ (varf x) (s.open ts)
  | app : Π {Γ : env V} {ef ea : exp V} {t₁ t₂ : typ V}
    , typing Γ ef (arr t₁ t₂)
    → typing Γ ea t₁
    → typing Γ (app ef ea) t₂
  | lam : Π {L : finset V} {Γ : env V} {e : exp V} {t₁ t₂ : typ V}
    , t₁.lc
    → (∀ x : V, x ∉ L → typing (insert ⟨x, ⟨0, t₁⟩⟩ Γ) (e.open_var x) t₂)
    → typing Γ (lam e) (arr t₁ t₂)
  | let_ : Π {L₁ L₂ : finset V} {Γ : env V} {e₁ e₂ : exp V} {s₁ : sch V} {t₂ : typ V}
    , (∀ xs : list V, fresh L₁ s₁.arity xs → typing Γ e₁ (s₁.open_vars xs))
    → (∀ x : V, x ∉ L₂ → typing (insert ⟨x, s₁⟩ Γ) (e₂.open_var x) t₂)
    → typing Γ (let_ e₁ e₂) t₂

end /- namespace -/ tts --------------------------------------------------------
