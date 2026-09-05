import CORALean.NN.Layers.ReLU

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

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

theorem not_differentiableAt_relu_zero : ¬ DifferentiableAt ℝ relu 0 := by
  intro h
  have hd : HasDerivAt relu (deriv relu 0) 0 := h.hasDerivAt
  -- to the right `relu` is the identity, to the left the constant zero
  have hid : HasDerivWithinAt relu 1 (Set.Ici 0) 0 :=
    (hasDerivWithinAt_id (0:ℝ) (Set.Ici 0)).congr (fun _ ht => max_eq_left ht) (max_self 0)
  have hz : HasDerivWithinAt relu 0 (Set.Iic 0) 0 :=
    (hasDerivWithinAt_const (0:ℝ) (Set.Iic (0:ℝ)) 0).congr (fun _ ht => max_eq_right ht)
      (max_self 0)
  have h1 : deriv relu 0 = 1 :=
    (uniqueDiffOn_Ici 0 0 Set.self_mem_Ici).eq_deriv _ hd.hasDerivWithinAt hid
  have h0 : deriv relu 0 = 0 :=
    (uniqueDiffOn_Iic 0 0 Set.self_mem_Iic).eq_deriv _ hd.hasDerivWithinAt hz
  rw [h1] at h0
  exact one_ne_zero h0

end CORALean.Real
