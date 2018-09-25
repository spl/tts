import data.equiv.basic

namespace tts ------------------------------------------------------------------

/-- An enumeration of the states in which a variable can occur with respect to
bindings. `occurs` is isomorphic to `bool` but more descriptive in naming. -/
@[derive decidable_eq]
inductive occurs : Type
| bound : occurs -- Referenced by a binding
| free  : occurs -- Not referenced by any binding (unbound)

namespace occurs ---------------------------------------------------------------

@[simp] def is_free : occurs → bool
| bound := ff
| free  := tt

@[simp] def of_free : bool → occurs
| ff := bound
| tt := free

def equiv_bool : occurs ≃ bool :=
⟨is_free, of_free, λ o, by cases o; simp, λ b, by cases b; simp⟩

@[reducible] instance : has_coe occurs bool :=
⟨is_free⟩

end /- namespace -/ occurs -----------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
