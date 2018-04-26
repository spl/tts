import data.finset

namespace list -----------------------------------------------------------------
variables {α : Type*} {a : α} {l : list α} [decidable_eq α]
variables {R : α → α → Prop} [decidable_rel R]

@[simp]
theorem pw_filter_idempotent : pw_filter R (pw_filter R l) = pw_filter R l :=
  pw_filter_eq_self.mpr (pairwise_pw_filter l)

@[simp]
theorem erase_dup_idempotent : erase_dup (erase_dup l) = erase_dup l :=
  pw_filter_idempotent

@[simp]
theorem to_finset_nil : to_finset (@nil α) = ∅ :=
  rfl

@[simp]
theorem to_finset_cons : to_finset (a :: l) = insert a (to_finset l) :=
  finset.eq_of_veq $ by by_cases h : a ∈ l; simp [finset.insert_val', multiset.erase_dup_cons, h]

theorem to_finset_card_of_nodup : l.nodup → l.to_finset.card = l.length :=
  begin
    induction l,
    case list.nil { simp },
    case list.cons : _ _ ih {
      intros nd,
      simp at nd,
      simp [finset.card_insert_of_not_mem ((not_iff_not_of_iff mem_to_finset).mpr nd.1),
            ih nd.2]
    }
  end

end /- namespace -/ list -------------------------------------------------------
