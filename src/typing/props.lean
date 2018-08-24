import .core
import sch

namespace tts ------------------------------------------------------------------
namespace typing ---------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {x : V} -- Variable names
variables {xs : list V} -- Lists of variable names
variables {e e₁ e₂ : exp V} -- Expressions
variables {t tx t₁ t₂ : typ V} -- Types
variables {ts : list (typ V)} -- Lists of types
variables {s : sch V} -- Type schemes
variables {Γ Γ₁ Γ₂ Γ₃ : env V} -- Environments

variables [decidable_eq V]

open exp
open typ
open env

theorem weaken_mid
: typing (Γ₁ ++ Γ₃) e t
→ uniq (Γ₁ ++ (Γ₂ ++ Γ₃))
→ typing (Γ₁ ++ (Γ₂ ++ Γ₃)) e t :=
  begin
    generalize Γh : Γ₁ ++ Γ₃ = Γ₁₃,
    intros T un_Γ₁_Γ₂_Γ₃,
    induction T generalizing Γ₁ Γ₃,
    case typing.varf : Γ x s ts un_Γ b ln_ts lc_ts wf_s {
      induction Γh,
      exact varf un_Γ₁_Γ₂_Γ₃ (mem_append_weaken b) ln_ts lc_ts wf_s,
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
    case typing.let_ : Ld Lb Γ ed eb sd tb Fd Fb ihd ihb {
      refine let_ (λ xs (ln_xs : xs.length = sd.arity) (nd : xs.nodup) (fr : finset.disjoint_list xs (Ld ∪ dom (Γ₁ ++ (Γ₂ ++ Γ₃)))), _)
                  (λ x (p : x ∉ Lb ∪ dom (Γ₁ ++ (Γ₂ ++ Γ₃))), _),
      show typing (Γ₁ ++ (Γ₂ ++ Γ₃)) ed (sd.open_vars xs), {
        exact ihd ln_xs nd (finset.disjoint_list_union.mp fr).1 Γh un_Γ₁_Γ₂_Γ₃
      },
      show typing (insert (x :~ sd) (Γ₁ ++ (Γ₂ ++ Γ₃))) (eb.open_var x) tb, {
        induction Γh,
        rw [finset.mem_union, decidable.not_or_iff_and_not] at p,
        rw ←append_insert,
        apply ihb p.1,
        { simp },
        { rw append_insert, exact uniq_insert.mpr ⟨p.2, un_Γ₁_Γ₂_Γ₃⟩ }
      }
    }
  end

theorem weaken
: typing Γ₂ e t
→ uniq (Γ₁ ++ Γ₂)
→ typing (Γ₁ ++ Γ₂) e t :=
  begin
    intro T,
    rw ←@append_empty_left _ Γ₂ at T,
    rw ←@append_empty_left _ (Γ₁ ++ Γ₂),
    exact weaken_mid T
  end

variables [finset.has_fresh V]

theorem subst_weaken
: typing (Γ₁ ++ (one (x :~ s) ++ Γ₂)) e₁ t
→ (∀ {ts : list (typ V)}, s.arity = ts.length → (∀ t ∈ ts, typ.lc t) → typing Γ₂ e₂ (s.open ts))
→ e₂.lc
→ typing (Γ₁ ++ Γ₂) (subst x e₂ e₁) t :=
  begin
    generalize Γh : Γ₁ ++ (one (x :~ s) ++ Γ₂) = Γ₁₂,
    intros T F lc_e₂,
    induction T generalizing Γ₁ Γ₂ x s e₂,
    case typing.varf : Γ y s₁ ts un_Γ b ln_ts lc_ts wf_s₁ {
      by_cases h : x = y; induction Γh,
      { /- h : x = y -/
        subst h,
        rw subst_varf,
        cases eq_sch_of_uniq_one_mid_of_mem_one_mid un_Γ b,
        apply weaken (F ln_ts lc_ts) (uniq_remove_mid un_Γ)
      },
      { /- h : x ≠ y -/
        rw subst_varf_of_ne h,
        exact varf (uniq_remove_mid un_Γ)
                   (mem_remove_mid_of_ne_var (ne.symm h) b)
                   ln_ts
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
    case typing.let_ : Ld Lb Γ ed eb sd tb Fd Fb ihd ihb {
      refine let_ (λ ys (ln_ys : ys.length = sd.arity) (nd : ys.nodup) (fr : finset.disjoint_list ys (Ld ∪ dom (Γ₁ ++ (one (x :~ s) ++ Γ₂)))), _)
                  (λ y (p : y ∉ Lb ∪ dom (Γ₁ ++ (one (x :~ s) ++ Γ₂))), _),
      show typing (Γ₁ ++ Γ₂) (subst x e₂ ed) (sd.open_vars ys), {
        exact ihd ln_ys nd (finset.disjoint_list_union.mp fr).1 Γh @F lc_e₂
      },
      show typing (insert (y :~ sd) (Γ₁ ++ Γ₂)) ((subst x e₂ eb).open_var y) tb, {
        induction Γh,
        rw [finset.mem_union, decidable.not_or_iff_and_not] at p,
        have : y ≠ x := ne_of_not_mem_dom_mid p.2,
        rw ←subst_open_var (ne.symm this) lc_e₂,
        rw ←append_insert,
        exact ihb p.1 (by simp) @F lc_e₂
      }
    }
  end

-- Expression substitution preserves typing.
theorem exp_subst_preservation
: typing (one (x :~ s) ++ Γ) e₁ t
→ (∀ {ts : list (typ V)}, s.arity = ts.length → (∀ t ∈ ts, typ.lc t) → typing Γ e₂ (s.open ts))
→ e₂.lc
→ typing Γ (subst x e₂ e₁) t :=
  begin
    intros T F lc_e₂,
    rw ←@append_empty_left _ (one (x :~ s) ++ Γ) at T,
    rw ←@append_empty_left _ Γ,
    exact subst_weaken T @F lc_e₂
  end

/-
Lemma typing_typ_subst : forall F Z U E t T,
  Z ∉ (env_fv E) ->
  type U ->
  E & F |= t ~: T ->
  E & (map (sch_subst Z U) F) |= t ~: (typ_subst Z U T).
Proof.
  introv. intros WVs Dis Typ. gen_eq (E & F) as G. gen F.
  induction Typ; introv EQ; subst; simpls typ_subst.
  rewrite~ sch_subst_open. apply* typing_var.
    binds_cases H0.
      apply* binds_concat_fresh.
       rewrite* sch_subst_fresh. use (fv_in_spec sch_fv B).
      auto*.
    rewrite~ sch_subst_arity. apply* typ_subst_type_list.
  apply_fresh* typing_abs as y.
   rewrite sch_subst_fold.
   apply_ih_map_bind* H1.
  apply_fresh* (@typing_let (sch_subst Z U M) (L1 ↑ {{Z}})) as y.
   simpl. intros Ys Fr.
   rewrite* <- sch_subst_open_vars.
   apply_ih_map_bind* H2.
  auto*.
Qed.
-/

-- Type substitution preserves typing.
theorem typ_subst_preservation
: x ∉ fv Γ₁
→ lc tx
→ typing (Γ₁ ++ Γ₂) e t
→ typing (Γ₁ ++ env.map (sch.subst x tx) Γ₂) e (typ.subst x tx t) :=
  begin
    generalize Γh : Γ₁ ++ Γ₂ = Γ₁₂,
    intros px lc_tx T,
    induction T generalizing Γ₁ Γ₂ x tx,
    case typing.varf : Γ y s ts un_Γ b ln_ts lc_ts wf_s {
      induction Γh,
      rw sch.subst_open lc_tx,
      apply typing.varf,
      { simp at un_Γ, simp [un_Γ] },
      { simp at b un_Γ ⊢,
        cases b,
        { exact or.inl (env.sch_subst_mem_of_not_mem_fv px b) },
        { exact or.inr (env.sch_subst_mem b) } },
      { simp [ln_ts] },
      { exact typ.map_subst_lc lc_tx lc_ts },
      { exact sch.subst_well_formed lc_tx wf_s },
    },
    case typing.app : Γ ef ea t₁ t₂ Tf Ta ihf iha {
      exact app (ihf Γh px lc_tx) (iha Γh px lc_tx)
    },
    case typing.lam : L Γ eb t₁ t₂ lc_t₁ T₂ ihb {
      simp only [typ.subst],
      dsimp at ihb, -- TODO: remove when done
/-
E & map (sch_subst Z U) F |= trm_abs t1 ~: typ_arrow (typ_subst Z U U0) (typ_subst Z U T)

⊢ typing (Γ₁ ++ map (sch.subst x tx) Γ₂) (exp.lam eb) (arr (subst x tx t₁) (subst x tx t₂))
-/
      refine lam (subst_lc lc_tx lc_t₁) (λ y (p : y ∉ L ∪ {x} ∪ fv t₁ ∪ fv t₂ ∪ fv Γ₁ ∪ fv Γ₂ ∪ dom (Γ₁ ++ Γ₂)), _),
      rw sch.subst_fold,
/-
Fr : y ∉ L ∪ {{Z}} ∪ dom E ∪ dom F ∪ trm_fv t1 ∪ typ_fv U ∪ typ_fv U0 ∪ typ_fv T ∪ env_fv E ∪ env_fv F

E & map (sch_subst Z U) F & y ~ sch_subst Z U (Sch 0 U0) |= t1 ^ y ~: typ_subst Z U T
----
⊢ typing (insert (y :~ sch.subst x tx ⟨0, t₁⟩) (Γ₁ ++ map (sch.subst x tx) Γ₂)) (open_var y eb) (subst x tx t₂)
-/
      rw ←append_insert,
      induction Γh,
      simp [decidable.not_or_iff_and_not] at p,
      sorry,
      -- apply ihb p.1,
      -- { rw ←append_insert, },
/-
      simp [decidable.not_or_iff_and_not] at p,
      -- induction Γh,
      rw ←append_insert,
      apply ihb p.1,
      {  },
      { rw ←append_insert, },
      { },
-/
    },
    case typing.let_ : Ld Lb Γ ed eb sd tb Fd Fb ihd ihb {
      sorry
    }
  end

/-
(** Iterated type substitution preserves typing *)
Lemma typing_typ_substs : forall Zs Us E t T,
  fresh (env_fv E) (length Zs) Zs ->
  types (length Zs) Us ->
  E |= t ~: T ->
  E |= t ~: (typ_substs Zs Us T).
Proof.
  induction Zs; destruct Us; simpl; introv Fr WU Tt;
   destruct Fr; inversions WU;
   simpls; try solve [ auto | contradictions* ].
  inversions H2. inversions H1. clear H2 H1.
  apply* IHZs. apply_empty* typing_typ_subst.
Qed.
-/

/-
theorem sch_open_of_open_vars
(ln_ts : s.arity = ts.length)
(lc_ts : ∀ t ∈ ts, typ.lc t)
(h : typing Γ e₂ (sch.open_vars (finset.fresh_list (sch.fv s ∪ typ.fv_list ts) s.arity) s))
: typing Γ e₂ (sch.open ts s) :=
  begin
    let nd := finset.fresh_list_nodup (sch.fv s ∪ typ.fv_list ts) ts.length,
    let ln := finset.fresh_list_length (sch.fv s ∪ typ.fv_list ts) ts.length,
    let dj := finset.fresh_list_disjoint (sch.fv s ∪ typ.fv_list ts) ts.length,
    rw sch.subst_list_intro nd ln dj lc_ts,
  end
-/

-- The following three theorems show the regularity of typing.

-- Typing implies a unique environment
theorem uniq_env (T : typing Γ e t) : Γ.uniq :=
  begin
    induction T; try { assumption },
    case typing.lam : L _ _ _ _ _ _ ihb {
      exact (uniq_insert.mp (ihb (finset.fresh_not_mem L))).2
    },
    case typing.let_ : _ Lb _ _ _ _ _ _ _ _ ihb {
      exact (uniq_insert.mp (ihb (finset.fresh_not_mem Lb))).2
    }
  end

-- Typing implies a locally-closed expression
theorem lc_exp (T : typing Γ e t) : e.lc :=
  begin
    induction T; simp [lc_body],
    case typing.app {
      tauto
    },
    case typing.lam {
      tauto
    },
    case typing.let_ : Ld _ _ _ _ sd _ _ _ ihd {
      split,
      exact ihd (finset.fresh_list_length Ld sd.arity)
                (finset.fresh_list_nodup Ld sd.arity)
                (finset.fresh_list_disjoint Ld sd.arity),
      tauto
    }
  end

-- Typing implies a locally-closed type
theorem lc_typ (T : typing Γ e t) : t.lc :=
  begin
    induction T,
    case typing.varf : _ _ _ _ _ _ ln_ts lc_ts wf_s {
      exact sch.open_lc wf_s ln_ts lc_ts
    },
    case typing.app : _ _ _ _ _ _ _ ihf {
      simp at ihf,
      tauto
    },
    case typing.lam : L _ _ _ _ lc_t₁ _ ihb {
      simp,
      exact ⟨lc_t₁, ihb (finset.fresh_not_mem L)⟩
    },
    case typing.let_ : _ Lb _ _ eb _ _ _ _ _ ihb {
      exact ihb (finset.fresh_not_mem Lb)
    }
  end

end /- namespace -/ typing -----------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
