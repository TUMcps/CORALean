import CORALean.ContSet.HPolytope.Float.Operations.NormalizeConstraints
import CORALean.ContSet.HPolytope.Float.Theorems.ScaleRowsOuter
import CORALean.ContSet.HPolytope.Float.Theorems.RecipUpPos

/-!
# The float `normalizeConstraints` keeps every point of the polytope in the domain

The divisors are positive (`recipUp_pos`), so `scaleRows_outer` applies: every point of the
polytope that lies in the domain meets the normalized rows. Outer over the domain, as
`reduceOverDomain_outer` is; the exact layer's `normalizeConstraints_exact` says the real operation
is the same set.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.normalizeConstraints_outer (P : HPolytope 𝕋 (Vec 𝕋 n))
    (dom : Interval (Vec 𝕋 n)) :
    P.construct ∩ dom.construct ⊆ (P.normalizeConstraints dom).construct ∩ dom.construct :=
  HPolytope.scaleRows_outer P _ _ (fun _ => HPolytope.recipUp_pos _)
    (fun _ => HPolytope.recipUp_pos _) dom

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
