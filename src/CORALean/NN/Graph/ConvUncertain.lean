import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import CORALean.ContSet.PolyZonotope.Real.Operations.PadBack
import CORALean.ContSet.PolyZonotope.Real.Operations.PadFront

/-!
# The graph convolutional layer at an uncertain graph

[1, Prop. 5]'s `H_k = 𝒫 H_{k-1} W`, both sets. Matrix multiplication is
bilinear, so this is `PolyZonotope.bilin` again, and `gcnShared` is the step at
a factor set the two sets *already* share. That is the primitive, because a
later step must reuse the edge factors it was handed rather than fresh ones.

`gcnUncertain` is its padded case, which is what only the *first* step needs:
`𝒫`'s factors are edges and residuals and `H`'s are node features, so `padBack`
gives `𝒫` the feature factors after its own and `padFront` gives `H` the edge
factors before its own, both at exponent zero. The two then read one factor
vector of `𝒫.p + H.p` while each ignores the other's half, and both sharing
hypotheses are `rfl`.

`W` is a known weight and stays a `map`, as at a fixed graph: it mixes features
and takes no part in the pairing, which is why `gcnLin` splits the same way.

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

/-- Matrix multiplication as a bilinear map, `bilin` at which is [1, Lemma 1]. -/
def GNN.matMulBilin (N F₁ F₂ : ℕ) : Mat ℝ N F₁ →ₗ[ℝ] Mat ℝ F₁ F₂ →ₗ[ℝ] Mat ℝ N F₂ :=
  LinearMap.mk₂ ℝ (fun X Y => X * Y) (fun X₁ X₂ Y => Matrix.add_mul X₁ X₂ Y)
    (fun c X Y => Matrix.smul_mul c X Y) (fun X Y₁ Y₂ => Matrix.mul_add X Y₁ Y₂)
    (fun c X Y => Matrix.mul_smul X c Y)

@[simp] theorem GNN.matMulBilin_apply (X : Mat ℝ N F₁) (Y : Mat ℝ F₁ F₂) :
    GNN.matMulBilin N F₁ F₂ X Y = X * Y := rfl


/-- One convolution at a factor set the two sets already share: `𝒫 H W`, with no
padding, so an edge recurring at a later step is the same factor. -/
def GNN.gcnShared (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) (hp : P.p = H.p) : PolyZonotope (Mat ℝ N F₂) :=
  (P.bilin (GNN.matMulBilin N N F₁) H hp).map (matMulRight W)

/-- A step keeps the factor set — `bilin` keeps `P.p` and `map` keeps `p` — which
is what a chain of steps at one graph rests on, and what the type does not say. -/
theorem GNN.gcnShared_p (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) (hp : P.p = H.p) :
    (GNN.gcnShared W P H hp).p = P.p := rfl


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s graph convolution at an uncertain graph: `gcnShared` after padding, the
two sets meeting over independent factors and `W` a known weight. -/
def GNN.gcnUncertain (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) : PolyZonotope (Mat ℝ N F₂) :=
  GNN.gcnShared W (P.padBack H.p) (H.padFront P.p) rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
