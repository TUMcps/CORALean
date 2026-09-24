import CORALean.ContSet.PolyZonotope.Real.Operations.PadBack
import CORALean.ContSet.PolyZonotope.Real.Operations.PadFront
import CORALean.NN.Graph.Operations.GcnShared

/-!
# The graph convolutional layer at an uncertain graph

[1, Prop. 5]'s graph convolution at an uncertain graph: `gcnShared` after
padding, the two sets meeting over independent factors and `W` a known
weight. `𝒫`'s factors are edges and residuals and `H`'s are node features, so
`padBack` gives `𝒫` the feature factors after its own and `padFront` gives `H`
the edge factors before its own, both at exponent zero.

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

/-- [1]'s graph convolution at an uncertain graph: `gcnShared` after padding, the
two sets meeting over independent factors and `W` a known weight. -/
def GNN.gcnUncertain (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) : PolyZonotope (Mat ℝ N F₂) :=
  GNN.gcnShared W (P.padBack H.p) (H.padFront P.p) rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
