import .core
import typ
import data.finset.fresh

namespace tts ------------------------------------------------------------------
namespace sch ------------------------------------------------------------------
variables {V : Type} -- Type of variable names
variables {ts : list (typ V)} -- Lists of types
variables {s : sch V} -- Schemes

variables [_root_.decidable_eq V] [finset.has_fresh V]

-- A well-formed schema opened with a list of types is locally-closed if all
-- types are locally-closed.
theorem open_lc
(wf_s : well_formed s)
(ln_ts : s.arity = ts.length)
(lc_ts : ∀ t ∈ ts, typ.lc t)
: typ.lc (sch.open ts s) :=
  begin
    unfold sch.open,
    cases wf_s with L wf,
    let L := sch.fv s ∪ typ.fv_list ts ∪ L,
    let nd := finset.fresh_list_nodup L ts.length,
    let ln := finset.fresh_list_length L ts.length,
    let dj := finset.fresh_list_disjoint_union.mp (finset.fresh_list_disjoint L ts.length),
    rw typ.subst_list_intro nd ln dj.1 lc_ts,
    rw ln_ts at wf,
    exact typ.subst_list_lc ln lc_ts (wf nd ln dj.2)
  end

end /- namespace -/ sch --------------------------------------------------------
end /- namespace -/ tts --------------------------------------------------------
