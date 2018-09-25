import env
import exp

namespace tts ------------------------------------------------------------------
variables {V : Type} [decidable_eq V] -- Type of variable names

open occurs exp typ sch

inductive typing : env V → exp V → typ V → Prop
  | var : Π {Γ : env V} {x : tagged V} {s : sch V} {ts : list (typ V)}
    , x :~ s ∈ Γ
    → s.arity = ts.length
    → (∀ (t : typ V), t ∈ ts → lc t)
    → lc s
    → typing Γ (var free x) (open_typs ts s)
  | app : Π {Γ : env V} {ef ea : exp V} {t₁ t₂ : typ V}
    , typing Γ ef (arr t₁ t₂)
    → typing Γ ea t₁
    → typing Γ (app ef ea) t₂
  | lam : Π {v} {Γ : env V} {eb : exp V} {t₁ t₂ : typ V} (L : finset (tagged V))
    , lc t₁
    → (∀ {x : tagged V}, x ∉ L → typing (insert ⟨x, ⟨0, t₁⟩⟩ Γ) (open_var x eb) t₂)
    → typing Γ (lam v eb) (arr t₁ t₂)
  | let_ : Π {v} {Γ : env V} {ed eb : exp V} (sd : sch V) {tb : typ V} (Ld Lb : finset (tagged V))
    , (∀ {xs : list (tagged V)}, xs.length = sd.arity → xs.nodup → (∀ x ∈ xs, x ∉ Ld) → typing Γ ed (open_vars xs sd))
    → (∀ {x : tagged V}, x ∉ Lb → typing (insert ⟨x, sd⟩ Γ) (open_var x eb) tb)
    → typing Γ (let_ v ed eb) tb

end /- namespace -/ tts --------------------------------------------------------
