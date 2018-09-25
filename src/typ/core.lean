import data.fresh occurs

namespace tts ------------------------------------------------------------------

/-- Grammar of types -/
@[derive decidable_eq]
inductive typ (V : Type) : Type
| var : occurs → tagged V → typ -- variable, bound or free
| arr : typ → typ → typ         -- function arrow

namespace typ ------------------------------------------------------------------
variables {V : Type} -- Type of variable names

open occurs

protected def repr [has_repr V] : typ V → string
| (var bound x)  := _root_.repr x.tag ++ "⟨" ++ _root_.repr x.val ++ "⟩"
| (var free x)   := _root_.repr x
| (arr t₁ t₂)    := "(" ++ t₁.repr ++ ") → (" ++ t₂.repr ++ ")"

instance [has_repr V] : has_repr (typ V) :=
⟨typ.repr⟩

end /- namespace -/ typ --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
