import CORALean.Global.Tensor

/-!
# The direction a rival label closes the gap in

How far label `j` closes the gap on label `l`: the direction a bound is asked
for, one per rival, to certify a classification. Used directly at the outputs
of concrete networks in `Examples`, and via `DisjointMisclassifiedOfBounds` and
`Classifies` at any network's image.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far label `j` closes the gap on label `l`: the direction each of the
`m - 1` bounds runs in. -/
def marginDir (m : ℕ) (j l : Fin m) : Vec ℝ m →ₗ[ℝ] ℝ :=
  (LinearMap.proj j : Vec ℝ m →ₗ[ℝ] ℝ) - (LinearMap.proj l : Vec ℝ m →ₗ[ℝ] ℝ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
