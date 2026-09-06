import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.PadBackPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.PadFrontPoint
import CORALean.NN.Graph.ConvUncertain

/-!
# The uncertain-graph convolution loses nothing

An *equality*, not an enclosure, and that is the point. The two factor sets are
disjoint, so every pair of admissible factor vectors is jointly admissible and
the image of the joint box is exactly the set of products `𝒫 H W` — the layer
itself gives nothing away.

The over-approximation an uncertain graph costs was already paid, once, by
`messagePassing_mem_enclosure`, where a non-affine inverse square root bought
residual factors. Paying it again here would be double counting, and stating
this step as an equality is what makes that visible.

Read against `point` on both sides rather than against the two sets, as
`bilin_exact` is: the claim is about the joint factor vector, `padBack_point`
and `padFront_point` splitting it into the half each set was written against.

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The padded pairing at a joint factor vector, read back as the product each
set contributes at its own half of it. -/
theorem GNN.aux_gcnUncertain_apply (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) (a : Fin (P.p + H.p) → ℝ) :
    matMulRight W ((GNN.matMulBilin N N F₁) ((P.padBack H.p).point a)
        ((H.padFront P.p).point fun k => a (Fin.cast rfl k)))
      = P.point (a ∘ Fin.castAdd H.p) * H.point (a ∘ Fin.natAdd P.p) * W := by
  rw [PolyZonotope.padBack_point, PolyZonotope.padFront_point]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1]'s uncertain-graph convolution is exactly the set of products the two
sets take at a joint factor vector. -/
theorem GNN.gcnUncertain_exact (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) :
    (fun a : Fin (P.p + H.p) → ℝ =>
        P.point (a ∘ Fin.castAdd H.p) * H.point (a ∘ Fin.natAdd P.p) * W)
        '' {a | ∀ k, |a k| ≤ 1}
      = (GNN.gcnUncertain W P H).construct := by -- --- PROOF ---
  have hb := PolyZonotope.bilin_exact (GNN.matMulBilin N N F₁) (P.padBack H.p)
    (H.padFront P.p) rfl
  have hm := PolyZonotope.map_exact (matMulRight W)
    ((P.padBack H.p).bilin (GNN.matMulBilin N N F₁) (H.padFront P.p) rfl)
  -- the layer is the pairing and then the weight, so the two images compose
  rw [GNN.gcnUncertain, ← hm, ← hb, ← Set.image_comp]
  exact Set.image_congr' fun a => (GNN.aux_gcnUncertain_apply W P H a).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
