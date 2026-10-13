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
# The inverse-square-root relaxation's slope over an uncertain degree

The relaxation's slope read over node `j`'s own degree interval
`[degreeInf, degreeSup]`, the box its uncertain degree is known to sit in.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The relaxation's slope over node `j`'s own degree interval. -/
noncomputable def GNN.sqrtSlope (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (j : Fin N) : ℝ :=
  R.slope (GNN.degreeInf A U j) (GNN.degreeSup A U j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
