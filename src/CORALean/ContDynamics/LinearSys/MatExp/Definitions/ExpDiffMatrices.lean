module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

/-!
# The matrices `s (e^{Ar} - I) + F` that enclose the variation of a point over `[0, r]`

`[1, Eq. 6]`'s `ΔR` is `M Z`, `M = {s(e^{Ar} - I) + F}` for `s ∈ [0, 1]` and `F` in the
correction matrix of [2] (`MatExp.correctionMatrix`); the weight `s` stands for `t/r` and cannot be
dropped, since `(e^{Ar} - I + F) Z` alone misses `Δx(0) = 0`.

## Inputs
* `A` – system matrix
* `r` – interval end
* `m` – Taylor order offset

## Output
* matrices enclosing the variation of a point over the interval

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
* [2] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The matrices `s (e^{Ar} - I) + F`, `s ∈ [0, 1]`, `F` of the correction matrix. -/
def MatExp.expDiffMatrices (A : Mat ℝ n n) (r : ℝ) (m : ℕ) : Set (Mat ℝ n n) :=
  {B | ∃ s ∈ Set.Icc (0 : ℝ) 1, ∃ F ∈ (MatExp.correctionMatrix A r (m + 2)).construct,
    B = s • (exp (r • A) - 1) + F}


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
