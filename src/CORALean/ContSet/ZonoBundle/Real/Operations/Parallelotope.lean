module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes

@[expose] public section

/-!
# `ZonoBundle.parallelotope`: the enclosing parallelotope

The `Ψ = Λ box(Λ⁻¹ Z_∩)` of [1, Eq. 2], with the box left as an argument: `B` carried through
the directions `Λ` as a zonotope of order 1. The paper says the split below is exact however
tightly the box is obtained, so the box is what a caller supplies, and
`ZonoBundle.enclosingBox` is one way to obtain it.

## Inputs
* `Λ` – edge directions
* `B` – box in the transformed coordinates

## Output
* the parallelotope along the directions enclosing the box

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
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

/-- `Ψ = Λ box(·)` of [1, Eq. 2]: the box `B` as a zonotope, mapped by the directions `Λ`. -/
noncomputable def ZonoBundle.parallelotope (Λ : Mat ℝ n n) (B : Interval (Vec ℝ n)) :
    Zonotope (Vec ℝ n) :=
  Zonotope.mtimes Λ B.zonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
