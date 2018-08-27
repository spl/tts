import sch

namespace tts ------------------------------------------------------------------

-- A pair of a variable and a type scheme.
def binding (V : Type) : Type :=
  Σ (_ : V), sch V

def binding.mk {V : Type} : V → sch V → binding V :=
  sigma.mk

infix ` :~ `:80 := binding.mk

variables {V : Type} -- Type of variable names

namespace binding --------------------------------------------------------------

-- Map a function over the type scheme of a binding.
protected
def map (f : sch V → sch V) : binding V → binding V :=
  sigma.map id (λ _, f)

end /- namespace -/ binding ----------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
