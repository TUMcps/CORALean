import CORALean.Global.Float.Instances.Real.Instances
import CORALean.NN.Layers.Definitions.Relaxation

/-!
# DeepZ's ReLU transformer

[1, Thm. 3.1]'s affine form for `y = ReLU(x)` over `x ∈ [l, u]`, Eq. (5), over ℝ: `x̂` when
`l > 0`, `0` when `u ≤ 0`, and otherwise `λ x̂ + μ + μ ε_new` with `λ = u / (u - l)` and
`μ = -u l / (2 (u - l))`, as a `Relaxation`: slope `λ`, offset `μ`, error `μ`. The interval
coefficients `[λl, λu]`, `[μl, μu]` the paper rounds to are left out, the tree paying rounding
into the error instead (FINDINGS.md); at ℝ they are the point values.

## References

* [1] G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". NeurIPS 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Thm. 3.1]'s Eq. (5): slope `λ`, offset and error `μ`. -/
noncomputable def deepZRelu : Relaxation ℝ where
  slope l u := if 0 < l then 1 else if u ≤ 0 then 0 else u / (u - l)
  offset l u := if 0 < l then 0 else if u ≤ 0 then 0 else -(u * l) / (2 * (u - l))
  error l u := if 0 < l then 0 else if u ≤ 0 then 0 else -(u * l) / (2 * (u - l))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
