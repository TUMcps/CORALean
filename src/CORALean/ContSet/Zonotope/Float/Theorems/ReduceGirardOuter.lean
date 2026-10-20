module

public import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByOuter

@[expose] public section

/-!
# `Zonotope.reduceGirard` over-approximates the zonotope

Below the order the zonotope is returned untouched, above it the claim is
`reduceBy_outer` at the partition Girard's rule chose.

## Inputs
* `Z` – zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* zonotope is contained in its Girard reduction
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceGirard_outer (Z : Zonotope (Vec 𝕋 n)) (o : ℕ) :
    Z.construct ⊆ (Z.reduceGirard o).construct := by
  unfold Zonotope.reduceGirard
  split_ifs with hlt
  · exact Zonotope.reduceBy_outer Z _
  · exact subset_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
