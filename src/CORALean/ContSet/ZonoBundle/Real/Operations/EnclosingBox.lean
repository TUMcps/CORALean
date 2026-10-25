module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `ZonoBundle.enclosingBox`: the box `Eq. 2` encloses by

`box(Λ⁻¹ Z_∩)` of [1, Eq. 2] as CORA computes it: the bundle mapped by `Λ⁻¹` member by member,
then the box of one member `i`, `ZonoBundle.interval`. The paper's `box` may be tighter, which
only helps; `ZonoBundle.split_union` holds at any box that encloses.

## Inputs
* `Λ` – direction matrix
* `zB` – zonotope bundle
* `i` – member index

## Output
* the box enclosing the bundle in the transformed coordinates

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `box(Λ⁻¹ Z_∩)` of [1, Eq. 2]: the box of the `i`-th member of the bundle mapped by `Λ⁻¹`. -/
noncomputable def ZonoBundle.enclosingBox (Λ : Mat ℝ n n) (zB : ZonoBundle (Vec ℝ n))
    (i : Fin zB.k) : Interval (Vec ℝ n) :=
  (zB.mtimes Λ⁻¹).interval i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
