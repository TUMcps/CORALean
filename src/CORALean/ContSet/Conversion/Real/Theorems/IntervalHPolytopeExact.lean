module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_HPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalMemHPolytopeIff

@[expose] public section

/-!
# A box as halfspaces

CORA's `polytope(interval)`: the `2n` constraints `xⱼ ≤ supⱼ` and `-xⱼ ≤ -infⱼ`.
Exact, and the only conversion into a halfspace description that costs nothing.

`HPolytope.unitBox` is this at `[-1, 1]ⁿ`, kept separate because a constrained
zonotope's domain names it constantly and should not carry an interval around.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- so the two descriptions denote the same set, with nothing given away
theorem Interval.hPolytope_exact (I : Interval (Vec ℝ n)) :
    (Interval.hPolytope I).construct = I.construct := by -- --- PROOF ---
  ext x
  constructor
  · intro hx i
    exact Interval.mem_hPolytope_iff.mp hx i
  · intro hx
    exact Interval.mem_hPolytope_iff.mpr fun i => hx i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
