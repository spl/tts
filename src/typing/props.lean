import .core

namespace tts ------------------------------------------------------------------
namespace typing ---------------------------------------------------------------
variables {V : Type} [decidable_eq V] -- Type of variable names
variables {x y : tagged V} -- Variables
variables {e ex e₁ : exp V} -- Expressions
variables {t : typ V} -- Types
variables {s s' : sch V} -- Type schemes
variables {Γ Γ₁ Γ₂ Γ₃ : env V} -- Environments
variables {L : finset (tagged V)} -- Variable sets

open finmap occurs exp typ sch

theorem weaken_middle :
  disjoint (dom Γ₁) (dom Γ₂) →
  disjoint (dom Γ₂) (dom Γ₃) →
  disjoint (dom Γ₁) (dom Γ₃) →
  typing (Γ₁ ∪ Γ₃) e t →
  typing (Γ₁ ∪ Γ₂ ∪ Γ₃) e t :=
begin
  generalize Γeq : Γ₁ ∪ Γ₃ = Γ₁₃,
  intros dj₁₂ dj₂₃ dj₁₃ T,
  induction T generalizing Γ₁ Γ₃,
  case typing.var : Γ x s ts b ln_eq lts ls {
    induction Γeq,
    exact var (mem_union_middle_left dj₁₃ dj₂₃ b) ln_eq lts ls,
  },
  case typing.app : Γ ef ea t₁ t₂ Tf Ta ihf iha {
    exact app (ihf Γeq dj₁₂ dj₂₃ dj₁₃) (iha Γeq dj₁₂ dj₂₃ dj₁₃),
  },
  case typing.lam : v Γ eb t₁ t₂ L lt₁ Ft₂ ihb {
    apply lam (L ∪ dom (Γ₁ ∪ Γ₂ ∪ Γ₃)) lt₁,
    introv nm,
    simp [not_or_distrib, and_assoc] at nm,
    rw [←insert_union, ←insert_union],
    induction Γeq,
    exact ihb nm.1 insert_union
      (disjoint_keys_insert_left.mpr ⟨nm.2.1, dj₁₂⟩)
      dj₂₃
      (disjoint_keys_insert_left.mpr ⟨nm.2.2.2, dj₁₃⟩),
  },
  case typing.let_ : v Γ ed eb sd tb Ld Lb _ _ ihd ihb {
    apply let_ sd (Ld ∪ dom (Γ₁ ∪ Γ₂ ∪ Γ₃)) (Lb ∪ dom (Γ₁ ∪ Γ₂ ∪ Γ₃)),
    { introv ln_eq nd nm,
      simp [not_or_distrib, and_assoc] at nm,
      exact ihd ln_eq nd (λ _ h, (nm _ h).1) Γeq dj₁₂ dj₂₃ dj₁₃ },
    { introv nm,
      simp [not_or_distrib, and_assoc] at nm,
      rw [←insert_union, ←insert_union],
      induction Γeq,
      exact ihb nm.1 insert_union
        (disjoint_keys_insert_left.mpr ⟨nm.2.1, dj₁₂⟩)
        dj₂₃
        (disjoint_keys_insert_left.mpr ⟨nm.2.2.2, dj₁₃⟩) }
  }
end

theorem weaken :
  disjoint (dom Γ₁) (dom Γ₂) →
  typing Γ₂ e t →
  typing (Γ₁ ∪ Γ₂) e t :=
begin
  intros dj T,
  rw ←empty_union Γ₂ at T,
  rw ←empty_union Γ₁ at ⊢,
  exact weaken_middle (finset.disjoint_empty_left _) dj (finset.disjoint_empty_left _) T
end

lemma ne_of_nm : x ∉ L ∪ dom (Γ₁ ∪ finmap.singleton (y :~ s) ∪ Γ₂) → y ≠ x :=
by simp [not_or_distrib]; tauto

lemma nmL_of_nm : x ∉ L ∪ dom (Γ₁ ∪ finmap.singleton (y :~ s) ∪ Γ₂) → x ∉ L :=
by simp [not_or_distrib]; tauto

lemma nmΓ₂_of_nm : x ∉ L ∪ dom (Γ₁ ∪ finmap.singleton (y :~ s) ∪ Γ₂) → x ∉ dom Γ₂ :=
by simp [not_or_distrib]; tauto

lemma nm_ins : x ∉ dom (Γ₁ ∪ Γ₂) → y ∉ L ∪ dom (Γ₁ ∪ finmap.singleton (x :~ s) ∪ Γ₂) →
  x ∉ dom (insert (binding.mk y s') Γ₁ ∪ Γ₂) :=
by simp [not_or_distrib]; tauto

theorem subst_weaken :
  disjoint (dom Γ₁) (dom Γ₂) →
  x ∉ dom (Γ₁ ∪ Γ₂) →
  lc ex →
  (∀ {ts : list (typ V)}, s.arity = ts.length → (∀ (t : typ V), t ∈ ts → lc t) → typing Γ₂ ex (open_typs ts s)) →
  typing (Γ₁ ∪ finmap.singleton (x :~ s) ∪ Γ₂) e t →
  typing (Γ₁ ∪ Γ₂) (subst x ex e) t :=
begin
  generalize Γeq : Γ₁ ∪ finmap.singleton (x :~ s) ∪ Γ₂ = Γ₁₂,
  intros dj nmd lex Tex T,
  induction T generalizing Γ₁ Γ₂ x s ex,
  case typing.var : Γ y s' ts b ln_eq lts ls {
    induction Γeq,
    have b : y :~ s' ∈ Γ₁ ∨ y :~ s' ∈ finmap.singleton (x :~ s) ∨ y :~ s' ∈ Γ₂ :=
      (or_assoc _ _).mp (or.imp_left mem_of_mem_union (mem_of_mem_union b)),
    by_cases h : x = y,
    { induction h,
      simp [not_or_distrib] at nmd,
      rcases b with m | m | m,
      { exact absurd (mem_keys_of_mem m) nmd.1 },
      { simp at m, induction m, simp [weaken dj (Tex ln_eq lts)] },
      { exact absurd (mem_keys_of_mem m) nmd.2 } },
    { rcases b with m | m | m,
      { simp [h, var ((mem_union dj).mpr (or.inl m)) ln_eq lts ls] },
      { simp at m, exact absurd m.1.symm h },
      { simp [h, var ((mem_union dj).mpr (or.inr m)) ln_eq lts ls] } } },
  case typing.app : Γ ef ea t₁ t₂ Tf Ta ihf iha {
    exact app (ihf Γeq dj nmd lex @Tex) (iha Γeq dj nmd lex @Tex) },
  case typing.lam : v Γ eb t₁ t₂ L lt₁ Ft₂ ihb {
    apply lam (L ∪ dom (Γ₁ ∪ finmap.singleton (x :~ s) ∪ Γ₂)) lt₁,
    induction Γeq,
    intros y nm,
    rw ←subst_open_var lex (ne_of_nm nm),
    rw ←insert_union,
    exact ihb (nmL_of_nm nm)
      (by rw [insert_union, insert_union])
      (disjoint_keys_insert_left.mpr ⟨by exact nmΓ₂_of_nm nm, dj⟩)
      (nm_ins nmd nm)
      lex
      @Tex },
  case typing.let_ : v Γ ed eb sd tb Ld Lb _ _ ihd ihb {
    dsimp at ihd ihb,
    apply let_ sd
      (Ld ∪ dom (Γ₁ ∪ finmap.singleton (x :~ s) ∪ Γ₂))
      (Lb ∪ dom (Γ₁ ∪ finmap.singleton (x :~ s) ∪ Γ₂)),
    { intros xs ln_eq nd nm,
      exact ihd ln_eq nd (λ _ h, nmL_of_nm (nm _ h)) Γeq dj nmd lex @Tex },
    { induction Γeq,
      intros y nm,
      rw ←subst_open_var lex (ne_of_nm nm),
      rw ←insert_union,
      exact ihb (nmL_of_nm nm)
        (by rw [insert_union, insert_union])
        (disjoint_keys_insert_left.mpr ⟨by exact nmΓ₂_of_nm nm, dj⟩)
        (nm_ins nmd nm)
        lex
        @Tex } }
end

-- Expression substitution preserves typing.
theorem exp_subst_preservation :
  x ∉ dom Γ →
  lc ex →
  (∀ {ts : list (typ V)}, s.arity = ts.length → (∀ (t : typ V), t ∈ ts → lc t) → typing Γ ex (open_typs ts s)) →
  typing (finmap.singleton (x :~ s) ∪ Γ) e₁ t →
  typing Γ (subst x ex e₁) t :=
begin
  intros nm lex Tex T,
  rw ←empty_union (finmap.singleton (x :~ s)) at T,
  rw ←empty_union Γ,
  exact subst_weaken (finset.disjoint_empty_left _) (by simp [nm]) lex @Tex T
end

-- Typing implies a locally-closed expression
theorem lc_exp (T : typing Γ e t) : lc e :=
begin
  induction T,
  case typing.var { simp },
  case typing.app { simp * },
  case typing.lam { simp [exp.lc_body, *], tauto },
  case typing.let_ : v _ ed _ _ _ _ _ _ _ ihd {
    dsimp at ihd,
    have : lc ed := ihd
      ((fresh.tagged v).pgenl_length_eq _ _)
      ((fresh.tagged v).pgenl_nodup _ _)
      (λ _, (fresh.tagged v).pgenl_not_mem),
    simp [exp.lc_body, *],
    tauto
  }
end

-- Typing implies a locally-closed type
theorem lc_typ (T : typing Γ e t) : lc t :=
begin
  induction T,
  case typing.var : _ _ _ _ _ ln_eq lts ls {
    exact lc_open_typs ls ln_eq lts },
  case typing.app : Γ ef ea t₁ t₂ Tf Ta ihf iha {
    simp at ihf,
    cases ihf with _ lt₂,
    exact lt₂ },
  case typing.lam : v _ _ _ _ L lt₁ _ ihb {
    dsimp at ihb,
    simp [lt₁, ihb ((fresh.tagged v).gen_not_mem L)] },
  case typing.let_ : v _ _ _ _ _ _ Lb _ _ _ ihb {
    exact ihb ((fresh.tagged v).gen_not_mem Lb) }
end

end /- namespace -/ typing -----------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
