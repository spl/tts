import .exp

namespace tts ------------------------------------------------------------------
variables {V : Type}  -- Type of variable names

open exp

-- Grammar of values
inductive value : exp V → Prop
  | lam  : Π {e : exp V}, (lam e).lc → value (lam e)

-- Reduction rules
inductive red : exp V → exp V → Prop
  | app₁  : Π {e₁ e₁' e₂ : exp V}, red e₁ e₁' →  e₂.lc →           red (app e₁ e₂)       (app e₁' e₂)
  | app₂  : Π {e₁ e₂ e₂' : exp V}, value e₁ →    red e₂ e₂' →      red (app e₁ e₂)       (app e₁ e₂')
  | lam   : Π {e₁ e₂ : exp V},     (lam e₁).lc → value e₂ →        red (app (lam e₁) e₂) (e₁.open e₂)
  | let₁  : Π {e₁ e₁' e₂ : exp V}, red e₁ e₁' →  e₂.lc_body →      red (let_ e₁ e₂)      (let_ e₁' e₂)
  | let₂  : Π {e₁ e₂ : exp V},     value e₁ →    (let_ e₁ e₂).lc → red (let_ e₁ e₂)      (e₂.open e₁)

end /- namespace -/ tts --------------------------------------------------------
