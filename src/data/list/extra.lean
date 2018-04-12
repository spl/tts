namespace list -----------------------------------------------------------------
variables {α : Type} {a a₁ a₂ : α} {l l₁ l₂ : list α} {n : ℕ} {p : α → Prop}

theorem nth_of_map {f : α → α} (p : f a = a)
: option.get_or_else (nth (map f l) n) a = f (option.get_or_else (nth l n) a) :=
  by induction l generalizing n; [skip, cases n]; simp [*, option.get_or_else]

theorem append_cons_left : l₁ ++ a :: l₂ = l₁ ++ [a] ++ l₂ :=
  by induction l₁; simp

inductive all_prop (p : α → Prop) : list α → Prop
| nil {} :                                            all_prop []
| cons   : Π {a : α} {l : list α}, p a → all_prop l → all_prop (a :: l)

theorem all_prop.singleton (pa : p a) : all_prop p [a] :=
  all_prop.cons pa all_prop.nil

theorem all_prop.append (ps₁ : all_prop p l₁) (ps₂ : all_prop p l₂)
: all_prop p (l₁ ++ l₂) :=
  begin
    induction l₁ with _ _ ih; simp,
    case list.nil { exact ps₂ },
    case list.cons : hd tl {
      cases ps₁ with _ _ p_hd ps_tl,
      exact all_prop.cons p_hd (ih ps_tl)
    }
  end

@[simp]
theorem all_prop_cons : all_prop p (a :: l) ↔ p a ∧ all_prop p l :=
  ⟨ λ p, by cases p with _ _ pa pl; exact ⟨pa, pl⟩
  , λ ⟨pa, pl⟩, all_prop.cons pa pl
  ⟩

theorem length_tail_eq_length_tail
{α β : Type} {a : α} {b : β} {la : list α} {lb : list β}
: length (a :: la) = length (b :: lb) → length la = length lb :=
  by simp [length]; exact nat.add_left_cancel

end /- namespace -/ list -------------------------------------------------------
