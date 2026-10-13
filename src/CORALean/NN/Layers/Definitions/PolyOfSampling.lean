module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.NN.Layers.Definitions.PolyRelaxation
public import CORALean.NN.Layers.Definitions.PolySampling

@[expose] public section

/-!
# The polynomial relaxation a fit and exact sampling buy

`computeApproxError` [1] over ℝ: the fit `c`, the exact sampled range of `σ - p` over `N + 1`
evenly spaced points, padded by `M · (u - l) / N`, its two ends averaged into the constant
coefficient so that what is left is a radius. A specification: the runnable relaxation samples
at a checked grid it cannot compute, and rounds; this is the one the convergence theory is about.
`c` is arbitrary — no soundness rests on it, only precision — and `N` is how much effort a box
gets.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The relaxation a fit and exact sampling buy; soundness is `ofSampling_sound`. -/
noncomputable def PolyRelaxation.ofSampling {n : ℕ} (σ : ℝ → ℝ) (c : ℝ → ℝ → Fin (n + 1) → ℝ)
    (M : ℝ → ℝ → ℝ) (N : ℝ → ℝ → ℕ) : CORALean.PolyRelaxation ℝ n where
  coeffs l u := shiftConst (c l u)
    ((sampleInf (fun x => σ x - evalPoly (c l u) x) l u (N l u)
      + sampleSup (fun x => σ x - evalPoly (c l u) x) l u (N l u)) / 2)
  error l u :=
    (sampleSup (fun x => σ x - evalPoly (c l u) x) l u (N l u)
      - sampleInf (fun x => σ x - evalPoly (c l u) x) l u (N l u)) / 2
      + M l u * ((u - l) / N l u)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
