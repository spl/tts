namespace list -----------------------------------------------------------------

inductive all_prop {α : Type} (p : α → Prop) : list α → Prop
| nil {} :                                            all_prop []
| cons   : Π {a : α} {l : list α}, p a → all_prop l → all_prop (cons a l)

end /- namespace -/ list -------------------------------------------------------
