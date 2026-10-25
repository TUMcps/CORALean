module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.NN.Layers.Definitions.Relaxation

@[expose] public section

/-!
# DeepZ's transformer for an S-shaped activation

[1, Thm. 3.2]'s affine form for `y = f(x)` over `x ∈ [l, u]`, Eq. (7), over ℝ, given `f` and
its derivative `df`: the constant `f(u)` when `l = u`, and otherwise `λ x̂ + μ₁ + μ₂ ε_new`
with `λ = min(f'(l), f'(u))`, `μ₁ = (f(u) + f(l) - λ (u + l)) / 2` and
`μ₂ = (f(u) - f(l) - λ (u - l)) / 2`. As a `Relaxation`: slope `λ`, offset `μ₁`, error `μ₂`.
The rounded interval coefficients are left out, as for `deepZRelu`.

Which `f` this is sound for is the question: `IsSShapedPrinted` is the class the paper's
footnote defines, and it is the wrong one.

## Inputs
* `f` – S-shaped activation function
* `df` – its derivative

## Output
* relaxation with DeepZ's slope, offset and error for the activation

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

/-- [1, Thm. 3.2]'s Eq. (7): slope `λ`, offset `μ₁`, error `μ₂`. -/
noncomputable def deepZSShape (f df : ℝ → ℝ) : Relaxation ℝ where
  slope l u := if l = u then 0 else min (df l) (df u)
  offset l u := if l = u then f u
    else (f u + f l - min (df l) (df u) * (u + l)) / 2
  error l u := if l = u then 0
    else (f u - f l - min (df l) (df u) * (u - l)) / 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
