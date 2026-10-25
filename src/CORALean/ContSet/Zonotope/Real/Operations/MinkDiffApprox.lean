module

public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffStretch
public import CORALean.Global.Tensor
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `Zonotope.minkDiffApprox`

CORA's `minkDiff(M, S)` at its default method `'approx'`, as [1]'s `aux_minkDiffZono` runs it for
a full-dimensional minuend outside `n = 2` and a subtrahend with generators: the minuend's
halfspaces `C x ≤ d` shifted inward by the subtrahend [2, Thm. 3], then [2, Prop. 6]'s closed form
`|C G| α = Δd` solved by `pinv`, and the minuend's generators scaled by `α`. `C` is an argument:
the first half of `polytope(M).A`, the normalised cross products of every `n - 1` generators
(`Zonotope.facetNormal`). `pinv` is written `(|C G|ᵀ |C G|)⁻¹ |C G|ᵀ`, which is `pinv` at full
column rank; Mathlib's `⁻¹` is `0` otherwise. Not a `MinkDiff` instance: nothing checks `α`, and
the result need not lie in the difference (`Zonotope.minkDiffApprox_not_inner`).

## Inputs
* `Z₁` – minuend
* `Z₂` – subtrahend
* `C` – halfspace normals of the minuend

## Output
* approximate Minkowski difference zonotope

## References

* [1] `contSet/@zonotope/minkDiff.m`, CORA, ll. 78, 114-138, 207-307.
* [2] M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794, 2015.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s `'approx'` at the minuend's halfspace normals `C` (the rows of `Horig`): `G` scaled by
`α = pinv(|C G|) Δd`, centered at `c⁽ᵐ⁾ - c⁽ˢ⁾`. -/
noncomputable def Zonotope.minkDiffApprox (Z₁ Z₂ : Zonotope (Vec ℝ n)) (C : Mat ℝ N n) :
    Zonotope (Vec ℝ n) :=
  -- `polytope.m`: the first half of `KorigTwice`, `C c + ∑ |C G|`
  let Korig : Vec ℝ N := fun i => C i ⬝ᵥ Z₁.c + ∑ j, |C i ⬝ᵥ Z₁.G j|
  -- [2, Thm. 3]'s shift, `C c⁽ˢ⁾ + ∑ |C G⁽ˢ⁾|`
  let delta_K : Vec ℝ N := fun i => C i ⬝ᵥ Z₂.c + ∑ k, |C i ⬝ᵥ Z₂.G k|
  let d : Vec ℝ N := fun i => Korig i - delta_K i
  let delta_d : Vec ℝ N := fun i => d i - C i ⬝ᵥ Z₁.c + C i ⬝ᵥ Z₂.c
  let A_abs : Mat ℝ N Z₁.h := Matrix.of fun i j => |C i ⬝ᵥ Z₁.G j|
  -- `alpha = pinv(A_abs) * delta_d`
  let alpha : Vec ℝ Z₁.h := (A_absᵀ * A_abs)⁻¹ *ᵥ (A_absᵀ *ᵥ delta_d)
  Z₁.minkDiffStretch Z₂ alpha

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
