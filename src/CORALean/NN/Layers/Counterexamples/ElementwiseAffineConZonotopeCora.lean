module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# `Layer.elementwiseAffineConZonotopeCora`: `evaluateConZonotope` of `nnElementwiseAffineLayer`

`nnElementwiseAffineLayer.m`, l. 150-154: `c = scale * c + offset; G = scale * G` with `scale` a
column vector and `c` a column vector of the same length `n`, so `scale * c` is an `n x 1` times an
`n x 1` matrix product, defined only for `n = 1` (`evaluatePolyZonotope` and the batch evaluation
use the elementwise `scale(:) .* c`). The product of mismatched matrices is `none`, standing for
MATLAB's error. Read from the source, not run.

`nnElementwiseAffineLayer([2;3], [0;1])` is valid, yet `evaluate(conZonotope([0;0], eye(2)))` stops
with the error, where `diag(scale) c + offset` is the answer.

## Inputs
* `c` – center vector

## Hypotheses
* none

## Conclusion
* the matrix product is an error while the elementwise product is defined
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- The center `scale * c` of `evaluateConZonotope`, for `scale` and `c` columns of lengths `m`
and `n`: the matrix product exists only when the inner dimensions agree, `m x 1` times `n x 1`
needs `1 = n`. `none` is the MATLAB error. -/
def Layer.elementwiseAffineConZonotopeCora (m n : ℕ) (scale : Fin m → ℝ) (c : Fin n → ℝ) :
    Option (Fin m → ℝ) :=
  if h : n = 1 then some (fun i => scale i * c ⟨0, by omega⟩) else none

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- With the two-element scale `(2, 3)` and a two-dimensional center, `scale * c` is an error,
while the elementwise product `(2 c₀, 3 c₁)` is defined. -/
theorem Layer.elementwiseAffineConZonotope_cora_crash (c : Fin 2 → ℝ) :
    Layer.elementwiseAffineConZonotopeCora 2 2 ![2, 3] c = none ∧
      ∃ r : Fin 2 → ℝ, r = fun i => ![2, 3] i * c i := by
  exact ⟨by simp [Layer.elementwiseAffineConZonotopeCora], _, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
