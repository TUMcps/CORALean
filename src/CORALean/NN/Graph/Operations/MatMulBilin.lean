import CORALean.ContSet.ContSet.ContSet

/-!
# Matrix multiplication as a bilinear map

`[1, Lemma 1]`'s bilinearity of `X, Y ↦ X * Y`, packaged as a `LinearMap.mk₂` so
`PolyZonotope.bilin` can be applied at it.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


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
