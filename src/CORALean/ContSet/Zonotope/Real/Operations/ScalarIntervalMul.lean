module

public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Operations.UnitIntervalMul

@[expose] public section

/-!
# An interval scalar times a zonotope

`[a, b] ⊗ Z`: the scalar `matZonotope(c, g)` of CORA, `c = (a + b)/2`, `g = (b - a)/2`, times a
zonotope [1]. Its center is `c z`, and the generators are `c G`, `g z` and every `g G` of `Z`,
each with a coefficient in `[-1, 1]`: `[a, b] ⊗ Z = c Z ⊕ [-1, 1] ⊗ (g Z)`, `[-1, 1] ⊗ ·` being
`unitIntervalMul`, [2, Eq. 11].

## References

* [1] `matrixSet/@matZonotope/mtimes.m`
* [2] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `c Z ⊕ [-1, 1] ⊗ (g Z)`. -/
noncomputable def Zonotope.scalarIntervalMul (a b : ℝ) (Z : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ n) :=
  (Zonotope.mtimes (((a + b) / 2) • (1 : Mat ℝ n n)) Z).plus
    (Zonotope.mtimes (((b - a) / 2) • (1 : Mat ℝ n n)) Z).unitIntervalMul

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
