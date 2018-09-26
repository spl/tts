import .core

namespace tts ------------------------------------------------------------------
namespace sch ------------------------------------------------------------------
variables {V : Type} [_root_.decidable_eq V] -- Type of variable names
variables {ts : list (typ V)} -- Lists of types
variables {s : sch V} -- Type schemes

-- A locally-closed schema opened with a list of types is locally-closed if all
-- types are locally-closed.
theorem lc_open_typs
  (ls : lc s)
  (ln_s_eq_ts : s.arity = ts.length)
  (lts : ∀ t ∈ ts, typ.lc t) :
  typ.lc (open_typs ts s) :=
begin
  cases ls with L ls,
  let L' := fv s ∪ typ.fv_list ts ∪ L,
  let FL' := ((freshL.tagged s.vars_nodup).pgen L').1,
  have ndL' : FL'.nodup := (freshL.tagged s.vars_nodup).pgen_nodup L',
  have ln_FL'_eq_s : FL'.length = s.arity :=
    freshL.tagged_length_eq L' s.vars_nodup,
  have nm_s_ts : ∀ x ∈ FL', x ∉ typ.fv s.type ∪ typ.fv_list ts :=
    λ _ h, ((freshL.tagged s.vars_nodup).pgen_mem_union h).1,
  have nm_L : ∀ x ∈ FL', x ∉ L :=
    λ _ h, ((freshL.tagged s.vars_nodup).pgen_mem_union h).2,
  have ln_FL'_eq_ts : FL'.length = ts.length := ln_FL'_eq_s.trans ln_s_eq_ts,
  rw [open_typs, typ.subst_list_intro ndL' ln_FL'_eq_ts nm_s_ts lts],
  exact typ.subst_list_lc ln_FL'_eq_ts lts (ls ndL' ln_FL'_eq_s nm_L)
end

end /- namespace -/ sch --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
