module

public import CORALean.ContSet.Zonotope.Real.Operations.Split
public import CORALean.ContSet.Zonotope.Real.Operations.BoxCora

@[expose] public section

/-!
# `Zonotope.splitCora`: `split(Z, N)` as CORA's code runs

`@zonotope/split.m` first replaces `Z` by its bounding box, `Z = zonotope(interval(Z))` (l. 46,
56, 106), then splits "generator `N`" of the box (`aux_splitOneDim`, `G(:,dim)`). The box is
built by `@interval/zonotope.m` as `zonotope([c, G(:,r ~= 0)])` (`Zonotope.boxCora`), which drops
the coordinates of zero width, so `N`, a coordinate of `Z`, is a generator index of the box and
`G(:,N)` is out of bounds once `N` exceeds the number of non-zero radii.
`split(zonotope([0;0],[1;0]))` loops `N = 1, 2` and stops at `N = 2`. Read from the source, not
run. `none` is the MATLAB error.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `Zsplit = aux_splitOneDim(zonotope(interval(Z)), N)`, `N` counted from `1`; `none`
is the out-of-bounds error of `G(:,N)`. -/
noncomputable def Zonotope.splitCora (Z : Zonotope (Vec ℝ n)) (N : ℕ) :
    Option (Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n)) :=
  if hN : 1 ≤ N ∧ N ≤ Z.boxCora.h then some (Z.boxCora.split ⟨N - 1, by omega⟩) else none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
