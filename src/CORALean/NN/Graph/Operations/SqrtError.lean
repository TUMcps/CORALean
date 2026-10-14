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
# How far the inverse-square-root relaxation may miss, at an uncertain degree

How far the affine map may miss `invSqrt` over node `j`'s own degree interval
`[degree, degreeSup]`.
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
  R.error (GNN.degree A j) (GNN.degreeSup A U j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
