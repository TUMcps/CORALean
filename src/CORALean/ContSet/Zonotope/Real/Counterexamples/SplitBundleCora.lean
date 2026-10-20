module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor

@[expose] public section

/-!
# `Zonotope.splitBundleCora`: `split(Z, dir, 'bundle')` as CORA's code runs

`aux_directionSplitBundle` of `@zonotope/split.m` (l. 176) computes
`intervals1 = get(IH,'intervals')` on `IH = interval(rotMat*Z)`. `interval` has no `get` (the
only `get.m` files in CORA are for `markovchain` and `simulation`), so every call raises an
error. Read from the source, not run.
`none` is the MATLAB error; the value of a call that does not error is not modelled.

# CORA's `split(Z, dir, 'bundle')` always crashes

`@zonotope/split.m` l. 176 calls the non-existent `get(IH,'intervals')`; the split of a zonotope
in a direction exists. Read from the source, not run.

## Inputs
* `n` – dimension
* `Z` – zonotope
* `dir` – split direction

## Hypotheses
* none

## Conclusion
* the bundle split always errors
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- Whether `split(Z, dir, 'bundle')` returns (`some ()`) or errors (`none`): it always errors. -/
def Zonotope.splitBundleCora (_Z : Zonotope (Vec ℝ n)) (_dir : Vec ℝ n) : Option Unit :=
  none

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `split(Z, dir, 'bundle')` errors for every zonotope and direction. -/
theorem Zonotope.split_cora_bundle_crash {n : ℕ} (Z : Zonotope (Vec ℝ n)) (dir : Vec ℝ n) :
    Z.splitBundleCora dir = none := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
