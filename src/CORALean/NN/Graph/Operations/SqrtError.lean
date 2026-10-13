import CORALean.NN.Graph.Operations.DegreeInf
import CORALean.NN.Graph.Operations.DegreeSup
import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.NN.Layers.Definitions.InvSqrt
import CORALean.NN.Layers.Definitions.InvSqrtRelaxation
import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Definitions.ScaleRounding
import CORALean.NN.Layers.Operations.LayerRelaxationBox
import CORALean.NN.Layers.Operations.RelaxationBox

/-!
# How far the inverse-square-root relaxation may miss, at an uncertain degree

How far the affine map may miss `invSqrt` over node `j`'s own degree interval
`[degreeInf, degreeSup]`.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far the affine map may miss `invSqrt` over that interval. -/
noncomputable def GNN.sqrtError (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (j : Fin N) : ℝ :=
  R.error (GNN.degreeInf A U j) (GNN.degreeSup A U j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
