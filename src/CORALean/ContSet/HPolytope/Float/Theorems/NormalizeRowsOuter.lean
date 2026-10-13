module

public import CORALean.ContSet.HPolytope.Float.Operations.NormalizeRows
public import CORALean.ContSet.HPolytope.Float.Theorems.ScaleRowsOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.RecipUpPos
public import CORALean.ContSet.HPolytope.Float.Theorems.RowScalePos

@[expose] public section

/-!
# The float `normalizeRows` keeps every point of the polytope in the domain

The divisors are positive (`rowScale_pos`, `recipUp_pos`), so `scaleRows_outer` applies: every
point of the polytope that lies in the domain meets the normalized rows. Outer over the domain,
as `reduceOverDomain_outer` is; the exact layer's `normalizeRows_exact` says the real operation
is the same set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
