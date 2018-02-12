import data.finset

namespace finset ---------------------------------------------------------------

class has_fresh (A : Type) :=
  (fresh : ∀ (s : finset A), Σ' a : A, a ∉ s)

-- Given `F : finset A` of `A` elements, produce a fresh `a : A` and a proof
-- that `a` is not a member of `F`.
def fresh {A : Type} [has_fresh A] (s : finset A) : Σ' (a : A), a ∉ s :=
  has_fresh.fresh s

end /- namespace -/ finset -----------------------------------------------------
