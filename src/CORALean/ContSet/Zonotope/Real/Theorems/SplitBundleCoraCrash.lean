module

public import CORALean.ContSet.Zonotope.Real.Operations.SplitBundleCora

@[expose] public section

/-!
# CORA's `split(Z, dir, 'bundle')` always crashes

`@zonotope/split.m` l. 176 calls the non-existent `get(IH,'intervals')`; the split of a zonotope
in a direction exists. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `split(Z, dir, 'bundle')` errors for every zonotope and direction. -/
theorem Zonotope.split_cora_bundle_crash {n : ℕ} (Z : Zonotope (Vec ℝ n)) (dir : Vec ℝ n) :
    Z.splitBundleCora dir = none := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
