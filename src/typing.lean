import .env
import .exp

namespace tts ------------------------------------------------------------------
variables {V : Type} [decidable_eq V] -- Type of variable names

open exp
open typ
open env

inductive typing : env V → exp V → typ V → Prop
  | varf : Π {Γ : env V} {x : V} {s : sch V} {ts : list (typ V)}
    , Γ.uniq
    → x :~ s ∈ Γ
    → lc_types s.arity ts
    → s.well_formed
    → typing Γ (varf x) (s.open ts)
  | app : Π {Γ : env V} {ef ea : exp V} {t₁ t₂ : typ V}
    , typing Γ ef (arr t₁ t₂)
    → typing Γ ea t₁
    → typing Γ (app ef ea) t₂
  | lam : Π {L : finset V} {Γ : env V} {eb : exp V} {t₁ t₂ : typ V}
    , t₁.lc
    → (∀ {x : V}, x ∉ L → typing (insert ⟨x, ⟨0, t₁⟩⟩ Γ) (eb.open_var x) t₂)
    → typing Γ (lam eb) (arr t₁ t₂)
  | let_ : Π {L₁ L₂ : finset V} {Γ : env V} {ed eb : exp V} {s₁ : sch V} {t₂ : typ V}
    , (∀ {xs : list V}, s₁.arity = xs.length → fresh xs L₁ → typing Γ ed (s₁.open_vars xs))
    → (∀ {x : V}, x ∉ L₂ → typing (insert ⟨x, s₁⟩ Γ) (eb.open_var x) t₂)
    → typing Γ (let_ ed eb) t₂

namespace typing ---------------------------------------------------------------
variables {e : exp V} -- Expressions
variables {t : typ V} -- Types
variables {Γ₁ Γ₂ Γ₃ : env V} -- Environments

theorem typing_weaken
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
      dsimp at ihd,
      dsimp at ihb,
      refine let_ (λ xs (ar_eq_len : s₁.arity = xs.length) (fr : fresh xs (L₁ ∪ dom (Γ₁ ++ (Γ₂ ++ Γ₃)))), _)
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

end /- namespace -/ typing -----------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
