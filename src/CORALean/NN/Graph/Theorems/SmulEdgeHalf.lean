module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# An edge weight split into a centre and a generator

One edge's weight split into the centre it shifts and the generator it
scales, which is the change of variable in matrix form: `λ = (1 + α)/2` at a
factor `α` in the unit interval around zero.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- One edge's weight split into the centre it shifts and the generator it
scales, which is the change of variable in matrix form. -/
theorem GNN.smul_edge_half (t : ℝ) (M : Mat ℝ N N) :
    ((1 + t) / 2 : ℝ) • M = (1/2 : ℝ) • M + t • ((1/2 : ℝ) • M) := by
  rw [smul_smul, ← add_smul]
  congr 1
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
