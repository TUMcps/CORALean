import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes

/-!
# `ZonoBundle.parallelotope`: the enclosing parallelotope

The `Ψ = Λ box(Λ⁻¹ Z_∩)` of [1, Eq. 2], with the box left as an argument: `B` carried through
the directions `Λ` as a zonotope of order 1. The paper says the split below is exact however
tightly the box is obtained, so the box is what a caller supplies, and
`ZonoBundle.enclosingBox` is one way to obtain it.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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
