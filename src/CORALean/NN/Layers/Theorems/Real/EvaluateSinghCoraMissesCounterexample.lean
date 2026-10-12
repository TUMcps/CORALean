import CORALean.NN.Layers.Definitions.EvaluateSinghCora
import CORALean.NN.Layers.Theorems.Real.DeepZSShapeCubeNotSound

/-!
# CORA's `'singh'` evaluation misses a true output of a network with activation `x³`

`nnActLayerFromHandle(@(x) x.^3, [], 1)` sets `monotonicity` for any handle, and
`options.nn.poly_method = 'singh'` is a documented option of `neuralNetwork/evaluate`. On the
network `x ↦ (x, 3 - x) ↦ (x³, (3 - x)³) ↦ x³ + (3 - x)³` and the input `[-1, 2]` the first neuron
gets the line `3 x + 2` with `d = 0` (`deepZSShape_cube_not_sound`), the second, on `[1, 4]`, the
line `34 - 3 x` with `d = 27`. The generators cancel, and the output is `[9, 63]`; the true output
at `x = 3/2` is `6.75`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem NN.evaluateSinghCora_misses_counterexample :
    SShapedPrinted (fun x : ℝ => x ^ 3) ∧ Monotone (fun x : ℝ => x ^ 3) ∧
      ∃ x : ℝ, -1 ≤ x ∧ x ≤ 2 ∧
        x ^ 3 + (3 - x) ^ 3 ∉ NN.evaluateSinghCora (fun x : ℝ => x ^ 3)
          (deriv fun x : ℝ => x ^ 3) 1 0 (-1) 3 (1 / 2) (3 / 2) := by -- --- PROOF ---
  obtain ⟨hS, hM, -⟩ := deepZSShape_cube_not_sound
  have hd : deriv (fun x : ℝ => x ^ 3) = fun x => 3 * x ^ 2 :=
    funext fun x => by rw [(hasDerivAt_pow 3 x).deriv]; norm_num
  refine ⟨hS, hM, 3 / 2, by norm_num, by norm_num, ?_⟩
  rintro ⟨s, e₁, e₂, hs, he₁, he₂, h⟩
  simp only [NN.evaluateSinghNeuronCora, hd] at h
  norm_num [abs_of_nonneg, abs_of_nonpos, min_def] at h
  have := (abs_le.mp he₂).1
  nlinarith [h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
