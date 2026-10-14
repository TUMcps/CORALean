module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# The direction a rival label closes the gap in

How far label `j` closes the gap on label `l`: the direction a bound is asked
for, one per rival, to certify a classification. Used directly at the outputs
of concrete networks in `Examples`, and via `DisjointMisclassifiedOfBounds` and
`Classifies` at any network's image.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far label `j` closes the gap on label `l`: the direction each of the
`m - 1` bounds runs in. -/
def marginDir (m : ℕ) (j l : Fin m) : Vec ℝ m →ₗ[ℝ] ℝ :=
  (LinearMap.proj j : Vec ℝ m →ₗ[ℝ] ℝ) - (LinearMap.proj l : Vec ℝ m →ₗ[ℝ] ℝ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
