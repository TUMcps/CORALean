module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# `Layer.elementwiseAffineConZonotopeCora`: `evaluateConZonotope` of `nnElementwiseAffineLayer`

`nn/layers/linear/nnElementwiseAffineLayer.m`, l. 150-154 (and `evaluateTaylm`, l. 136-139):

```
[scale,offset] = obj.aux_getScaleAndOffset();
c = scale * c + offset;
G = scale * G;
```

`aux_getScaleAndOffset` returns `scale` as a column vector (`aux_getPaddedParameter`: `p(:)` for a
vector parameter, and with `inputSize` unset the padded size is `1`), and `c` is a column vector
of the same length `n` (`conversionConZonoStarSet`), so `scale * c` is an `n x 1` times an `n x 1`
matrix product, defined only for `n = 1`. `evaluatePolyZonotope` and the batch evaluation use the
elementwise `scale(:) .* c`. `nnBatchNormLayer` inherits both methods. The product of two matrices
is `none` when the inner dimensions differ, which stands for MATLAB's error `Incorrect dimensions
for matrix multiplication`. Read from the source, not run.

# CORA's elementwise affine layer stops on a constrained zonotope

`nnElementwiseAffineLayer([2;3], [0;1])` is a valid layer (the constructor takes column vectors),
and `evaluate(conZonotope([0;0], eye(2)))` stops with the error, where `diag(scale) c + offset`
is the answer. Read from the source, not run.
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
