import CORALean.ContSet.HPolytope.Float.Operations.NormalizeRows
import CORALean.ContSet.HPolytope.Float.Theorems.ScaleRowsOuter
import CORALean.ContSet.HPolytope.Float.Theorems.RecipUpPos
import CORALean.ContSet.HPolytope.Float.Theorems.RowScalePos

/-!
# The float `normalizeRows` keeps every point of the polytope in the domain

The divisors are positive (`rowScale_pos`, `recipUp_pos`), so `scaleRows_outer` applies: every
point of the polytope that lies in the domain meets the normalized rows. Outer over the domain,
as `reduceOverDomain_outer` is; the exact layer's `normalizeRows_exact` says the real operation
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

theorem HPolytope.normalizeRows_outer (p : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n))
    (dom : Interval (Vec 𝕋 n)) :
    P.construct ∩ dom.construct ⊆ (P.normalizeRows p dom).construct ∩ dom.construct :=
  HPolytope.scaleRows_outer P _ _ (HPolytope.rowScale_pos p P) (fun _ => HPolytope.recipUp_pos _)
    dom

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
