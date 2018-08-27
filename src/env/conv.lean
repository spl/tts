/-

import .core

namespace tts ------------------------------------------------------------------
namespace env ------------------------------------------------------------------
namespace conv -----------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {fs : sch V → sch V} -- Type scheme function
variables {b : binding V} -- Bindings
variables {Γ Γ₁ Γ₂ Γ₃ : list (binding V)} -- Binding lists

protected
theorem binding : binding.map fs b = (b.var :~ fs (b.sch)) :=
  by cases b; simp

protected
theorem empty : has_emptyc.emptyc (env V) = env.mk [] :=
  rfl

protected
theorem insert : insert b (env.mk Γ) = env.mk (b :: Γ) :=
  rfl

protected
theorem one : one b = env.mk (b :: []) :=
  rfl

protected
theorem append : env.mk Γ₁ ++ env.mk Γ₂ = env.mk (Γ₁ ++ Γ₂) :=
  rfl

protected
theorem mem : b ∈ env.mk Γ = (b ∈ Γ) :=
  rfl

protected
theorem map : map fs (env.mk Γ) = env.mk (Γ.map (binding.map fs)) :=
  rfl

variables [decidable_eq V]

protected
theorem fv : fv (env.mk Γ) = binding_list.fv Γ :=
  rfl

protected
theorem dom : dom (env.mk Γ) = binding_list.dom Γ :=
  rfl

protected
theorem disjoint : disjoint (env.mk Γ₁) (env.mk Γ₂) = binding_list.disjoint Γ₁ Γ₂ :=
  rfl

protected
theorem uniq : uniq (env.mk Γ) = binding_list.uniq Γ :=
  rfl

end /- namespace -/ conv -------------------------------------------------------
end /- namespace -/ env --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------

-/
