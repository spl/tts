import .defs

namespace tts ------------------------------------------------------------------
namespace typing ---------------------------------------------------------------
variables {V : Type} [decidable_eq V] -- Type of variable names
variables {x : V} -- Variable names
variables {e e₁ e₂ : exp V} -- Expressions
variables {t : typ V} -- Types
variables {s : sch V} -- Type schemes
variables {Γ Γ₁ Γ₂ Γ₃ : env V} -- Environments

open exp
open typ
open env

theorem typing_weaken_mid
: typing (Γ₁ ++ Γ₃) e t
→ uniq (Γ₁ ++ (Γ₂ ++ Γ₃))
→ typing (Γ₁ ++ (Γ₂ ++ Γ₃)) e t :=
  begin
    generalize Γh : Γ₁ ++ Γ₃ = Γ₁₃,
    intros T un_Γ₁_Γ₂_Γ₃,
    induction T generalizing Γ₁ Γ₃,
    case typing.varf : Γ x s ts un_Γ b lc_ts wf_s {
      induction Γh,
      exact varf un_Γ₁_Γ₂_Γ₃ (mem_append_weaken b) lc_ts wf_s,
    },
    case typing.app : Γ ef ea t₁ t₂ Tf Ta ihf iha {
      exact app (ihf Γh un_Γ₁_Γ₂_Γ₃) (iha Γh un_Γ₁_Γ₂_Γ₃),
    },
    case typing.lam : L Γ eb t₁ t₂ lc_t₁ F₂ ihb {
      refine lam lc_t₁ (λ x (p : x ∉ L ∪ dom (Γ₁ ++ (Γ₂ ++ Γ₃))), _),
      show typing (insert (x :~ ⟨0, t₁⟩) (Γ₁ ++ (Γ₂ ++ Γ₃))) (eb.open_var x) t₂, {
        induction Γh,
        rw [finset.mem_union, decidable.not_or_iff_and_not] at p,
        rw ←append_insert,
        apply ihb p.1,
        { simp },
        { rw append_insert, exact uniq_insert.mpr ⟨p.2, un_Γ₁_Γ₂_Γ₃⟩ }
      }
    },
    case typing.let_ : L₁ L₂ Γ ed eb s₁ t₂ F₁ F₂ ihd ihb {
      refine let_ (λ xs (ar_eq_len : s₁.arity = xs.length) (fr : fresh (L₁ ∪ dom (Γ₁ ++ (Γ₂ ++ Γ₃))) xs), _)
                  (λ x (p : x ∉ L₂ ∪ dom (Γ₁ ++ (Γ₂ ++ Γ₃))), _),
      show typing (Γ₁ ++ (Γ₂ ++ Γ₃)) ed (s₁.open_vars xs), {
        exact ihd ar_eq_len (fresh_union.mp fr).1 Γh un_Γ₁_Γ₂_Γ₃
      },
      show typing (insert (x :~ s₁) (Γ₁ ++ (Γ₂ ++ Γ₃))) (eb.open_var x) t₂, {
        induction Γh,
        rw [finset.mem_union, decidable.not_or_iff_and_not] at p,
        rw ←append_insert,
        apply ihb p.1,
        { simp },
        { rw append_insert, exact uniq_insert.mpr ⟨p.2, un_Γ₁_Γ₂_Γ₃⟩ }
      }
    }
  end

theorem typing_weaken
: typing Γ₂ e t
→ uniq (Γ₁ ++ Γ₂)
→ typing (Γ₁ ++ Γ₂) e t :=
  begin
    intro T,
    rw ←@append_empty_left _ Γ₂ at T,
    rw ←@append_empty_left _ (Γ₁ ++ Γ₂),
    exact typing_weaken_mid T
  end

variables [finset.has_fresh V]

theorem typing_subst_weaken
: typing (Γ₁ ++ (one (x :~ s) ++ Γ₂)) e₁ t
→ (∀ {ts}, lc_types s.arity ts → typing Γ₂ e₂ (s.open ts))
→ e₂.lc
→ typing (Γ₁ ++ Γ₂) (subst x e₂ e₁) t :=
  begin
    generalize Γh : Γ₁ ++ (one (x :~ s) ++ Γ₂) = Γ₁₂,
    intros T F lc_e₂,
    induction T generalizing Γ₁ Γ₂ x s e₂,
    case typing.varf : Γ y s₁ ts un_Γ b lc_ts wf_s₁ {
      by_cases h : x = y; induction Γh,
      { /- h : x = y -/
        subst h,
        rw subst.varf.eq,
        cases eq_sch_of_uniq_one_mid_of_mem_one_mid un_Γ b,
        apply typing_weaken (F lc_ts) (uniq_remove_mid un_Γ)
      },
      { /- h : x ≠ y -/
        rw subst.varf.ne h,
        exact varf (uniq_remove_mid un_Γ)
                   (mem_remove_mid_of_ne_var (ne.symm h) b)
                   lc_ts
                   wf_s₁
      }
    },
    case typing.app : Γ ef ea t₁ t₂ Tf Ta ihf iha {
      exact app (ihf Γh @F lc_e₂) (iha Γh @F lc_e₂)
    },
    case typing.lam : L Γ eb t₁ t₂ lc_t₁ F₂ ihb {
      refine lam lc_t₁ (λ y (p : y ∉ L ∪ dom (Γ₁ ++ (one (x :~ s) ++ Γ₂))), _),
      show typing (insert (y :~ ⟨0, t₁⟩) (Γ₁ ++ Γ₂)) ((subst x e₂ eb).open_var y) t₂, {
        induction Γh,
        rw [finset.mem_union, decidable.not_or_iff_and_not] at p,
        have : y ≠ x := ne_of_not_mem_dom_mid p.2,
        rw ←subst_open_var (ne.symm this) lc_e₂,
        rw ←append_insert,
        exact ihb p.1 (by simp) @F lc_e₂
      }
    },
    case typing.let_ : L₁ L₂ Γ ed eb s₁ t₂ F₁ F₂ ihd ihb {
      dsimp at ihd, dsimp at ihb,
      refine let_ (λ ys (ar_eq_len : s₁.arity = ys.length) (fr : fresh (L₁ ∪ dom (Γ₁ ++ (one (x :~ s) ++ Γ₂))) ys), _)
                  (λ y (p : y ∉ L₂ ∪ dom (Γ₁ ++ (one (x :~ s) ++ Γ₂))), _),
      show typing (Γ₁ ++ Γ₂) (subst x e₂ ed) (s₁.open_vars ys), {
        exact ihd ar_eq_len (fresh_union.mp fr).1 Γh @F lc_e₂
      },
      show typing (insert (y :~ s₁) (Γ₁ ++ Γ₂)) ((subst x e₂ eb).open_var y) t₂, {
        induction Γh,
        rw [finset.mem_union, decidable.not_or_iff_and_not] at p,
        have : y ≠ x := ne_of_not_mem_dom_mid p.2,
        rw ←subst_open_var (ne.symm this) lc_e₂,
        rw ←append_insert,
        exact ihb p.1 (by simp) @F lc_e₂
      }
    }
  end

theorem typing_subst
: typing (one (x :~ s) ++ Γ) e₁ t
→ (∀ {ts}, lc_types s.arity ts → typing Γ e₂ (s.open ts))
→ e₂.lc
→ typing Γ (subst x e₂ e₁) t :=
  begin
    intros T F lc_e₂,
    rw ←@append_empty_left _ (one (x :~ s) ++ Γ) at T,
    rw ←@append_empty_left _ Γ,
    exact typing_subst_weaken T @F lc_e₂
  end

end /- namespace -/ typing -----------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
