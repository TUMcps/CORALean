module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Data.EReal.Basic

@[expose] public section

/-!
# `HPolytope.rowLowerCora`: the lower-bound update of `aux_isInterval`

`@polytope/representsa_.m` (`aux_isInterval`, l. 236-312), for a row `constraint` with offset
`offsets(c)`: if exactly one entry `idx` is nonzero (`nnz(idx) == 1`) and it is negative,
`lb(idx) = max([-offsets(c) / constraint_norm, lb(idx)])`; otherwise `lb` is not changed
(`-Inf`). This is the value the row proposes for `lb(j)`, tolerance `0`. Read from the source,
not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The proposal of the row `f x ≤ c` for `lb(j)`. -/
noncomputable def HPolytope.rowLowerCora (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) (j : Fin n) : EReal :=
  open Classical in
  if f (Pi.single j 1) < 0 ∧ ∀ i, i ≠ j → f (Pi.single i 1) = 0  -- nnz(idx) == 1, negative entry
  then ((-c / |f (Pi.single j 1)| : ℝ) : EReal)                  -- -offsets(c) / constraint_norm
  else ⊥

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
