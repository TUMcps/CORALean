module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Matrix multiplication as a bilinear map

`[1, Lemma 1]`'s bilinearity of `X, Y ↦ X * Y`, packaged as a `LinearMap.mk₂` so
`PolyZonotope.bilin` can be applied at it.

## Inputs
* `N` – number of rows of the left factor
* `F₁` – shared inner dimension
* `F₂` – number of columns of the right factor

## Output
* matrix multiplication as a bilinear map

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Matrix multiplication as a bilinear map, `bilin` at which is [1, Lemma 1]. -/
def GNN.matMulBilin (N F₁ F₂ : ℕ) : Mat ℝ N F₁ →ₗ[ℝ] Mat ℝ F₁ F₂ →ₗ[ℝ] Mat ℝ N F₂ :=
  LinearMap.mk₂ ℝ (fun X Y => X * Y) (fun X₁ X₂ Y => Matrix.add_mul X₁ X₂ Y)
    (fun c X Y => Matrix.smul_mul c X Y) (fun X Y₁ Y₂ => Matrix.mul_add X Y₁ Y₂)
    (fun c X Y => Matrix.mul_smul X c Y)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
