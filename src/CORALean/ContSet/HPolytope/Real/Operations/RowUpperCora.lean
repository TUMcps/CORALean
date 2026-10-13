import CORALean.ContSet.HPolytope.Real.HPolytope
import Mathlib.Data.EReal.Basic

/-!
# `HPolytope.rowUpperCora`: the upper-bound update of `aux_isInterval`

`@polytope/representsa_.m` (`aux_isInterval`, l. 236-312), for a row `constraint` with offset
`offsets(c)`: if exactly one entry `idx` is nonzero (`nnz(idx) == 1`) and it is positive,
`ub(idx) = min([offsets(c) / constraint_norm, ub(idx)])`; otherwise `ub` is not changed (`Inf`).
This is the value the row proposes for `ub(j)`, tolerance `0`. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The proposal of the row `f x ≤ c` for `ub(j)`. -/
noncomputable def HPolytope.rowUpperCora (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) (j : Fin n) : EReal :=
  open Classical in
  if 0 < f (Pi.single j 1) ∧ ∀ i, i ≠ j → f (Pi.single i 1) = 0  -- nnz(idx) == 1, positive entry
  then ((c / |f (Pi.single j 1)| : ℝ) : EReal)                   -- offsets(c) / constraint_norm
  else ⊤

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
