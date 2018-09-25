import typ.open

namespace tts ------------------------------------------------------------------
namespace typ ------------------------------------------------------------------
variables {V : Type} [_root_.decidable_eq V] -- Type of variable names
variables {t t₁ t₂ : typ V} -- Types
variables {ts : list (typ V)} -- Lists of types

open occurs

/-- Locally-closed type -/
inductive lc : typ V → Prop
| var : Π (x : tagged V),                  lc (var free x)
| arr : Π {t₁ t₂ : typ V}, lc t₁ → lc t₂ → lc (arr t₁ t₂)

/-- Locally-closed body of a type scheme with a given arity -/
def lc_body (n : ℕ) (t : typ V) : Prop :=
∃ (L : finset (tagged V)),
∀ {xs : list (tagged V)},
xs.nodup →
xs.length = n →
(∀ {x : tagged V}, x ∈ xs → x ∉ L) →
lc (open_vars xs t)

@[simp] theorem lc_var_free (x : tagged V) : lc (var free x) :=
lc.var x

@[simp] theorem lc_arr : lc (arr t₁ t₂) ↔ lc t₁ ∧ lc t₂ :=
⟨λ l, by cases l with _ _ _ l₁ l₂; exact ⟨l₁, l₂⟩, λ ⟨l₁, l₂⟩, lc.arr l₁ l₂⟩

-- Opening a locally-closed type is the identity
@[simp] theorem open_typs_id (l : lc t) : open_typs ts t = t :=
by induction t; cases l; simp [open_typs, *]

end /- namespace -/ typ --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
