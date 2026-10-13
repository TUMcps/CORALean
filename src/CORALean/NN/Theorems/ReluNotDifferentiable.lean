module

public import CORALean.NN.Layers.Definitions.Relu
public import CORALean.NN.Layers.Operations.Relu
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-!
# ReLU has no derivative at zero

The reason `Layer.sensitivity` carries no obligation and gets no agreement
theorem here: the commonest activation of all is not differentiable, so a
`Layer` field holding a derivative would be a lie and a `HasFDerivAt` hypothesis
on the layer would exclude it.

The two one-sided derivatives are `1` and `0`, and `Ici 0` and `Iic 0` both
determine a derivative uniquely, so a two-sided one would have to be both.

What follows for `Layer.relu` is that its sensitivity is whatever `fderiv`
returns where the layer is not differentiable, which is zero and is junk;
CORA reads the subgradient there instead, and either choice is a heuristic.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem not_differentiableAt_relu_zero : ¬ DifferentiableAt ℝ Real.relu 0 := by -- --- PROOF ---
  intro h
  have hd : HasDerivAt Real.relu (deriv Real.relu 0) 0 := h.hasDerivAt
  -- to the right `Real.relu` is the identity, to the left the constant zero
  have hid : HasDerivWithinAt Real.relu 1 (Set.Ici 0) 0 :=
    (hasDerivWithinAt_id (0:ℝ) (Set.Ici 0)).congr (fun _ ht => max_eq_left ht) (max_self 0)
  have hz : HasDerivWithinAt Real.relu 0 (Set.Iic 0) 0 :=
    (hasDerivWithinAt_const (0:ℝ) (Set.Iic (0:ℝ)) 0).congr (fun _ ht => max_eq_right ht)
      (max_self 0)
  have h1 : deriv Real.relu 0 = 1 :=
    (uniqueDiffOn_Ici 0 0 Set.self_mem_Ici).eq_deriv _ hd.hasDerivWithinAt hid
  have h0 : deriv Real.relu 0 = 0 :=
    (uniqueDiffOn_Iic 0 0 Set.self_mem_Iic).eq_deriv _ hd.hasDerivWithinAt hz
  rw [h1] at h0
  exact one_ne_zero h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
