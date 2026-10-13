module

public import CORALean.ContSet.Zonotope.Real.Operations.Abs
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

/-!
# What `Zonotope.abs` keeps of its input

`abs` is not an enclosure: the zonotope with generators `(1, 1)` and `(1, -1)` contains
`(2, 0)`, whose entrywise absolute value is not on the segment `abs` leaves. What it keeps is the
box corner: the vertex `|c| + Σ |gⱼ|` of `abs Z` (all coefficients `1`) bounds every point's
entrywise absolute value, and `abs` is idempotent and has the same corner.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The corner `|c| + Σ |gⱼ|` is a vertex of `abs Z`. -/
theorem Zonotope.abs_corner_mem (Z : Zonotope (Vec ℝ n)) :
    (fun i => Z.absBound i) ∈ Z.abs.construct :=
  ⟨fun _ => 1, fun _ => by simp, funext fun i => by
    simp [Zonotope.abs, Zonotope.absBound, Finset.sum_apply]; rfl⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
