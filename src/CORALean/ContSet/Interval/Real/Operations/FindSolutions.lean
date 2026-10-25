module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Finset.Image
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `Interval.findSolutions`

[1, Alg. 3], `FIND SOLUTIONS(v, B, α)`: the cut points of `Σᵢ xᵢ = α` at or adjacent to the
vertex `v` of the box `[0, b₁] × … × [0, bₙ]`. With `α' = α - Σᵢ vᵢ`, `v` itself if `α' = 0`,
otherwise one point per coordinate with `vᵢ = 0` and `bᵢ > α'`: `v` with its `i`-th coordinate
raised to `α'`, on the edge from `v` upwards.

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection Problem".
      INFOCOMP Journal of Computer Science, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- `FIND SOLUTIONS`, the box given by its upper corner `b`. -/
noncomputable def Interval.findSolutions (b : Vec ℝ n) (α : ℝ) (v : Vec ℝ n) :
    Finset (Vec ℝ n) :=
  let α' := α - ∑ i, v i                                      -- 2
  if α' = 0 then {v}                                          -- 3-4: `v` is a solution vertex
  else (Finset.univ.filter fun i => α' < b i ∧ v i = 0).image -- 6
    fun i => Function.update v i α'                           -- 7: `t ← v`, `tᵢ ← α'`

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
