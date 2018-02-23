import data.finset

namespace finset ---------------------------------------------------------------
variables {α : Type*} [decidable_eq α]

theorem insert_union_distrib (a : α) (s t : finset α) : insert a (s ∪ t) = insert a s ∪ insert a t :=
  by simp [ext]

class has_fresh (A : Type) :=
  (fresh : ∀ (s : finset A), Σ' a : A, a ∉ s)

-- Given `F : finset A` of `A` elements, produce a fresh `a : A` and a proof
-- that `a` is not a member of `F`.
def fresh {A : Type} [has_fresh A] (s : finset A) : Σ' (a : A), a ∉ s :=
  has_fresh.fresh s

end /- namespace -/ finset -----------------------------------------------------
