module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor
public import CORALean.ContSet.Zonotope.Real.Operations.Split

@[expose] public section

/-!
# `Zonotope.boxRadiusCora`: `rad(interval(Z))`

The radius of the bounding box of a zonotope at coordinate `i`, `∑ⱼ |G j i|`, the `r` that
`@interval/zonotope.m` reads (`r = rad(I)`) when `split` boxes its operand.

# `Zonotope.boxCora`: `zonotope(interval(Z))` as CORA builds it

`@interval/zonotope.m` ends with `G = diag(r); Z = zonotope([c, G(:,r ~= 0)])`: the generators of
zero radius are dropped, so the box has one generator per coordinate of non-zero radius, in
order. Its center is the center of `Z`. Read from the source, not run.

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


-- The model: CORA's code as printed, kept only to be refuted.
/-- `rad(interval(Z))` at coordinate `i`. -/
noncomputable def Zonotope.boxRadiusCora (Z : Zonotope (Vec ℝ n)) (i : Fin n) : ℝ :=
  ∑ j, |Z.G j i|

end CORALean.Real

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
open Classical in
/-- `zonotope(interval(Z))`: `zonotope([c, G(:,r ~= 0)])` with `G = diag(r)`. -/
noncomputable def Zonotope.boxCora (Z : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  let nz := (List.finRange n).filter fun i => Z.boxRadiusCora i ≠ 0
  ⟨nz.length, Z.c, fun k => Z.boxRadiusCora (nz.get k) • (Pi.single (nz.get k) 1 : Fin n → ℝ)⟩

end CORALean.Real

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
