import CORALean.ContSet.HPolytope.Real.HPolytope
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# The polyhedral asymmetric norm

`[1, Def. 3]`: for a polytope `{η_i x ≤ h_i}` with every `h_i ≠ 0`,
`S_P(x) = max {0, η₁ x / h₁, …, η_s x / h_s}`. The `0` makes it a fold of `max` from `0`
over the rows.

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {s n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `S_P(x)`, `[1, Def. 3]`. -/
noncomputable def HPolytope.polyNorm (H : Mat ℝ s n) (h : Vec ℝ s) (x : Vec ℝ n) : ℝ :=
  Finset.univ.fold max 0 fun i => (H *ᵥ x) i / h i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
