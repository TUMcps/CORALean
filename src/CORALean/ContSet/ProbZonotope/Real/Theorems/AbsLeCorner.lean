module

public import CORALean.ContSet.ProbZonotope.Real.Operations.Abs
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsCorner

@[expose] public section

/-!
# What `ProbZonotope.abs` keeps of its input

`abs` is not a set operation on the probabilistic zonotope (`abs_not_mem`). What it keeps is the
corner `|c| + Σ |gⱼ|` of the new mean zonotope, which bounds the entrywise absolute value of every
possible mean: the box around the result's means contains `|μ|` for every mean `μ`, the covariance
untouched.
Outer, as a box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.abs_le_corner (P : ProbZonotope n) {μ : Vec ℝ n}
    (hμ : μ ∈ P.Z.construct) (i : Fin n) : |μ i| ≤ P.abs.Z.absBound i :=
  Zonotope.abs_le_abs_corner hμ i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
