import data.fresh
import data.finset
import occurs

namespace tts ------------------------------------------------------------------

open occurs

/-- Grammar of expressions -/
inductive exp (V : Type) : Type
| var  : occurs → tagged V → exp -- variable, bound or free
| app  : exp → exp → exp         -- function application
| lam  : V → exp → exp           -- lambda-abstraction
| let_ : V → exp → exp → exp     -- let-abstraction

namespace exp ------------------------------------------------------------------
variables {V : Type} -- Type of variable names

protected def repr [has_repr V] : exp V → string
| (var bound x)  := _root_.repr x.tag ++ "⟨" ++ _root_.repr x.val ++ "⟩"
| (var free x)   := _root_.repr x
| (app ef ea)    := "(" ++ ef.repr ++ ") (" ++ ea.repr ++ ")"
| (lam v eb)     := "λ " ++ _root_.repr v ++ " . " ++ eb.repr
| (let_ v ed eb) := "let " ++ _root_.repr v ++ " = " ++ ed.repr ++ " in " ++ eb.repr

instance [has_repr V] : has_repr (exp V) :=
⟨exp.repr⟩

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
