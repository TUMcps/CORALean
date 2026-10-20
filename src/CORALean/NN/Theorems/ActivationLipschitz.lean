module

public import CORALean.NN.Layers.Layer
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-!
# What an activation layer does to a distance

An activation is the same scalar function on every neuron, and the metric on `Vec ℝ n` is the
supremum over the coordinates, so the layer's constant is `σ`'s own: the worst coordinate is the
only one that matters. In a Euclidean metric the constant would be the same but the argument would
not. Stated at the function `fun x i => σ (x i)`, which is the `eval` of `Layer.activation`, of
`Layer.activationPoly` and of `Layer.activationPolyRefinable` alike — a relaxation changes what is
enclosed, never what is computed.

## Inputs
* `σ` – activation function
* `K` – Lipschitz constant
* `n` – layer width

## Hypotheses
* `hσ` – the activation is Lipschitz with that constant

## Conclusion
* the layer's map is Lipschitz with the same constant
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.lipschitzWith_activation_eval {σ : ℝ → ℝ} {K : NNReal} (hσ : LipschitzWith K σ)
    (n : ℕ) : LipschitzWith K (fun (x : Vec ℝ n) i => σ (x i)) := by -- --- PROOF ---
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)]
  intro i
  -- the coordinate's own distance is under the supremum one, and `σ` scales it
  exact le_trans (hσ.dist_le_mul (x i) (y i))
    (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) K.coe_nonneg)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
