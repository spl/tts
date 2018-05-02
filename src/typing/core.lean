import env
import exp

namespace tts ------------------------------------------------------------------
variables {V : Type} [decidable_eq V] -- Type of variable names

open exp
open typ

inductive typing : env V → exp V → typ V → Prop
  | varf : Π {Γ : env V} {x : V} {s : sch V} {ts : list (typ V)}
    , Γ.uniq
    → x :~ s ∈ Γ
    → s.arity = ts.length
    → (∀ t ∈ ts, typ.lc t)
    → s.well_formed
    → typing Γ (varf x) (s.open ts)
  | app : Π {Γ : env V} {ef ea : exp V} {t₁ t₂ : typ V}
    , typing Γ ef (arr t₁ t₂)
    → typing Γ ea t₁
    → typing Γ (app ef ea) t₂
  | lam : Π {L : finset V} {Γ : env V} {eb : exp V} {t₁ t₂ : typ V}
    , t₁.lc
    → (∀ {x : V}, x ∉ L → typing (insert ⟨x, ⟨0, t₁⟩⟩ Γ) (eb.open_var x) t₂)
    → typing Γ (lam eb) (arr t₁ t₂)
  | let_ : Π {Ld Lb : finset V} {Γ : env V} {ed eb : exp V} {sd : sch V} {tb : typ V}
    , (∀ {xs : list V}, xs.length = sd.arity → xs.nodup → finset.disjoint_list xs Ld → typing Γ ed (sd.open_vars xs))
    → (∀ {x : V}, x ∉ Lb → typing (insert ⟨x, sd⟩ Γ) (eb.open_var x) tb)
    → typing Γ (let_ ed eb) tb

end /- namespace -/ tts --------------------------------------------------------
