import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import CORALean.NN.Graph.Operations.MatMulBilin

/-!
# One convolution step at a shared factor set

[1, Prop. 5]'s `H_k = 𝒫 H_{k-1} W`, both sets, at a factor set the two sets
*already* share. Matrix multiplication is bilinear, so this is
`PolyZonotope.bilin` at `matMulBilin`, followed by `map` at the known weight
`W`. That is the primitive, because a later step must reuse the edge factors
it was handed rather than fresh ones.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
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

/-- One convolution at a factor set the two sets already share: `𝒫 H W`, with no
padding, so an edge recurring at a later step is the same factor. -/
def GNN.gcnShared (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) (hp : P.p = H.p) : PolyZonotope (Mat ℝ N F₂) :=
  (P.bilin (GNN.matMulBilin N N F₁) H hp).map (matMulRight W)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
