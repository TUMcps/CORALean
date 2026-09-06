import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import CORALean.ContSet.PolyZonotope.Real.Operations.PadBack
import CORALean.ContSet.PolyZonotope.Real.Operations.PadFront

/-!
# The graph convolutional layer at an uncertain graph

[1]'s `H_k = 𝒫 H_{k-1} W` with `𝒫` and `H` both sets. Matrix multiplication is
bilinear, so this is `PolyZonotope.bilin` again — but at *independent* factors:
`𝒫`'s are edges and residuals, `H`'s are node features, and `bilin` pairs two
sets over one shared factor set.

Padding closes that gap and nothing else has to change. `padBack` gives `𝒫` the
feature factors after its own and `padFront` gives `H` the edge factors before
its own, both at exponent zero, so the two now read one factor vector of
`𝒫.p + H.p` while each still ignores the other's half. Both sharing hypotheses
are then `rfl`.

`W` is a known weight and stays a `map`, as at a fixed graph: it mixes features
and takes no part in the pairing, which is why `gcnLin` splits the same way.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}

/-- Matrix multiplication as a bilinear map, which is what `bilin` propagates. -/
def GNN.matMulBilin (N F₁ F₂ : ℕ) : Mat ℝ N F₁ →ₗ[ℝ] Mat ℝ F₁ F₂ →ₗ[ℝ] Mat ℝ N F₂ :=
  LinearMap.mk₂ ℝ (fun X Y => X * Y) (fun X₁ X₂ Y => Matrix.add_mul X₁ X₂ Y)
    (fun c X Y => Matrix.smul_mul c X Y) (fun X Y₁ Y₂ => Matrix.mul_add X Y₁ Y₂)
    (fun c X Y => Matrix.mul_smul X c Y)

@[simp] theorem GNN.matMulBilin_apply (X : Mat ℝ N F₁) (Y : Mat ℝ F₁ F₂) :
    GNN.matMulBilin N F₁ F₂ X Y = X * Y := rfl


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s graph convolution at an uncertain graph: `𝒫 H W`, the two sets over
independent factors and `W` a known weight. -/
def GNN.gcnUncertain (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) : PolyZonotope (Mat ℝ N F₂) :=
  ((P.padBack H.p).bilin (GNN.matMulBilin N N F₁) (H.padFront P.p) rfl).map (matMulRight W)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
