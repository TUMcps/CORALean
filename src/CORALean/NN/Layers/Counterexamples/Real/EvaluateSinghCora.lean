module

public import Mathlib.Data.Real.Basic
public import CORALean.NN.Layers.Theorems.Real.DeepZSShapeCubeNotSound

@[expose] public section

/-!
# `evaluatePolyZonotopeNeuron` with `poly_method = 'singh'`, order 1, as printed

CORA's `evaluatePolyZonotopeNeuron.m` bounds the neuron's input `[l, u]` and evaluates the line of
`computeApproxPoly(obj, l, u, order, 'singh')`, for `order == 1` [1, Thm. 3.2]: slope
`lambda = min(df(l), df(u))`, error `d = mu2` as a fresh generator.

On `x ↦ (x, 3 - x) ↦ (x³, (3 - x)³) ↦ x³ + (3 - x)³` over `[-1, 2]` the neurons get the lines
`3 x + 2` (`d = 0`) and `34 - 3 x` (`d = 27`), the generators cancel, and the output is `[9, 63]`,
but the true output at `x = 3/2` is `6.75`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the cube is monotone yet some true output lies outside CORA's result

## References

* [1] G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". Advances in Neural Information Processing Systems, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- The neuron step on `c + g ε`: center, generator, error `d`. -/
noncomputable def NN.evaluateSinghNeuronCora (f df : ℝ → ℝ) (c g : ℝ) : ℝ × ℝ × ℝ :=
  let l := c - |g|
  let u := c + |g|
  let lambda := min (df l) (df u)
  let mu1 := 0.5 * (f u + f l - lambda * (u + l))
  let mu2 := 0.5 * (f u - f l - lambda * (u - l))
  (lambda * c + mu1, lambda * g, mu2)


-- The model: CORA's code as printed, kept only to be refuted.
/-- The output interval of the network on the input zonotope `c + g ε`. -/
noncomputable def NN.evaluateSinghCora (f df : ℝ → ℝ) (a₁ b₁ a₂ b₂ c g : ℝ) : Set ℝ :=
  let n₁ := NN.evaluateSinghNeuronCora f df (a₁ * c + b₁) (a₁ * g)
  let n₂ := NN.evaluateSinghNeuronCora f df (a₂ * c + b₂) (a₂ * g)
  {y | ∃ s e₁ e₂ : ℝ, |s| ≤ 1 ∧ |e₁| ≤ 1 ∧ |e₂| ≤ 1 ∧
    y = (n₁.1 + n₂.1) + (n₁.2.1 + n₂.2.1) * s + n₁.2.2 * e₁ + n₂.2.2 * e₂}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NN.evaluateSinghCora_misses_counterexample : -- --- CONCL ---
    IsSShapedPrinted (fun x : ℝ => x ^ 3) ∧ Monotone (fun x : ℝ => x ^ 3) ∧
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
