import tactic.basic

meta def name.update_suffix : name → (string → string) → name
| name.anonymous        _ := name.anonymous
| (name.mk_string s p)  f := name.mk_string (f s) p
| (name.mk_numeral n p) _ := name.mk_numeral n p

namespace tactic ---------------------------------------------------------------
namespace interactive ----------------------------------------------------------

open interactive
open interactive.types

meta def note_all_applied (p : parse texpr) : tactic unit :=
  do e ← to_expr p,
     et ← infer_type e,
     guard et.is_pi <|> fail format!"'note_all_applied' expects a function, got '{et}'",
     ctx ← local_context,
     ctx.for_each $ λ h, do
       ht ← infer_type h,
       tactic.try $ do
         unify ht et.binding_domain,
         note (h.local_pp_name.update_suffix (++ "'")) none (e.mk_app [h])

end /- namespace -/ interactive ------------------------------------------------
end /- namespace -/ tactic -----------------------------------------------------
