import sch

namespace tts ------------------------------------------------------------------

-- A pair of a variable and a type scheme.
@[derive decidable_eq]
structure binding (V : Type) : Type :=
  (var : V)
  (sch : sch V)

infix ` :~ `:80 := binding.mk

variables {V : Type} -- Type of variable names

namespace binding --------------------------------------------------------------

-- Map a function over the type scheme of a binding.
protected
def map (f : tts.sch V → tts.sch V) : binding V → binding V
  | (binding.mk x s) := binding.mk x (f s)

end /- namespace -/ binding ----------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
