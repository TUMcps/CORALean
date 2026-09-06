import CORALean.NN.Layer

/-!
# What an activation layer does to a distance

An activation is the same scalar function on every neuron, and the metric on
`Vec ℝ n` is the supremum over the coordinates, so the layer's constant is `σ`'s
own: the worst coordinate is the only one that matters and no summing over
neurons happens. In a Euclidean metric the constant would be the same but the
argument would not.

Stated at the function `fun x i => σ (x i)`, which is the `eval` of
`Layer.activation`, of `Layer.activationPoly` and of
`Layer.activationPolyRefinable` alike — a relaxation changes what is propagated,
never what is computed.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.lipschitzWith_activation_eval {σ : ℝ → ℝ} {K : NNReal} (hσ : LipschitzWith K σ)
    (n : ℕ) : LipschitzWith K (fun (x : Vec ℝ n) i => σ (x i)) := by -- --- PROOF ---
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)]
  intro i
  -- the coordinate's own distance is under the supremum one, and `σ` scales it
  exact le_trans (hσ.dist_le_mul (x i) (y i))
    (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) K.coe_nonneg)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
