import .core
import typ

namespace tts ------------------------------------------------------------------
namespace sch ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables [_root_.decidable_eq V]
variables {ts : list (typ V)} -- Lists of types
variables {s : sch V} -- Schemes

-- A locally-closed schema opened with a list of types is locally-closed if all
-- types are locally-closed.
theorem open_lc
(v : V)
(ls : lc s)
(ln_eq_s : s.arity = ts.length)
(lts : ∀ t ∈ ts, typ.lc t)
: typ.lc (open_typs ts s) :=
  begin
    cases ls with L ls,
    let L' := fv s ∪ typ.fv_list ts ∪ L,
    let FL' := ((fresh.tagged v).pgenl L' ts.length).1,
    have dL' : FL'.nodup := (fresh.tagged v).pgenl_nodup L' ts.length,
    have ln_eq_FL' : FL'.length = ts.length :=
      (fresh.tagged v).pgenl_length L' ts.length,
    have Fs_ts : ∀ x ∈ FL', x ∉ typ.fv s.type ∪ typ.fv_list ts :=
      λ _ h, ((fresh.tagged v).pgenl_mem_union h).1,
    have FL : ∀ x ∈ FL', x ∉ L :=
      λ _ h, ((fresh.tagged v).pgenl_mem_union h).2,
    unfold open_typs,
    rw typ.subst_list_intro dL' ln_eq_FL' Fs_ts lts,
    exact typ.subst_list_lc ln_eq_FL' lts (ls dL' (ln_eq_FL'.trans ln_eq_s.symm) FL)
  end

end /- namespace -/ sch --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
