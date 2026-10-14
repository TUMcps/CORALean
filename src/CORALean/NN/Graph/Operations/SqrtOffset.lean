module

public import CORALean.NN.Graph.Operations.Degree
public import CORALean.NN.Graph.Operations.DegreeSup
public import CORALean.NN.Layers.Definitions.Enclosure
public import CORALean.NN.Layers.Definitions.InvSqrt
public import CORALean.NN.Layers.Definitions.InvSqrtRelaxation
public import CORALean.NN.Layers.Definitions.Relaxation
public import CORALean.NN.Layers.Definitions.ScaleRounding
public import CORALean.NN.Layers.Operations.LayerRelaxationBox
public import CORALean.NN.Layers.Operations.RelaxationBox

@[expose] public section

/-!
# The inverse-square-root relaxation's offset over an uncertain degree

The relaxation's offset read over node `j`'s own degree interval
`[degree, degreeSup]`, the box its uncertain degree is known to sit in.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {N m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The relaxation's offset over that same interval. -/
noncomputable def GNN.sqrtOffset (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (j : Fin N) : ℝ :=
  R.offset (GNN.degree A j) (GNN.degreeSup A U j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
