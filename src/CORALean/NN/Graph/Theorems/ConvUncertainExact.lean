module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.PadBackPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PadFrontPoint
public import CORALean.NN.Graph.Operations.GcnUncertain
public import CORALean.NN.Graph.Theorems.GcnSharedExact

@[expose] public section

/-!
# The uncertain-graph convolution loses nothing

[1, Prop. 5] as an *equality*, not an enclosure, and that is the point. The two
factor sets are disjoint, so every pair of admissible factor vectors is jointly
admissible and the image of the joint box is exactly the set of products
`𝒫 H W` — the layer itself gives nothing away.

The over-approximation an uncertain graph costs was already paid, once, by
`messagePassing_mem_enclosure`, where a non-affine inverse square root bought
residual factors. Paying it again here would be double counting, and stating
this step as an equality is what makes that visible.

`gcnShared_exact` is the whole proof: `gcnUncertain` *is* the shared step at the
padded pair, so its guarantee is that one read back through `padBack_point` and
`padFront_point`, which split the joint factor vector into the half each set was
written against. Read over `point` rather than over the two sets, as
`bilin_exact` is, since the claim is about the joint factor vector.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The padded pair at a joint factor vector, read back as the product each set
contributes at its own half of it. -/
theorem GNN.aux_gcnUncertain_apply (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) (a : Fin (P.p + H.p) → ℝ) : -- --- STMT ---
    (P.padBack H.p).point a
        * (H.padFront P.p).point (fun k => a (Fin.cast (rfl : (P.p + H.p) = (P.p + H.p)) k)) * W
      = P.point (a ∘ Fin.castAdd H.p) * H.point (a ∘ Fin.natAdd P.p) * W := by -- --- PROOF ---
  rw [PolyZonotope.padBack_point, PolyZonotope.padFront_point]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1]'s uncertain-graph convolution is exactly the set of products the two
sets take at a joint factor vector. -/
theorem GNN.gcnUncertain_exact (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) : -- --- STMT ---
    (fun a : Fin (P.p + H.p) → ℝ =>
        P.point (a ∘ Fin.castAdd H.p) * H.point (a ∘ Fin.natAdd P.p) * W)
        '' {a | ∀ k, |a k| ≤ 1}
      = (GNN.gcnUncertain W P H).construct := by -- --- PROOF ---
  -- the layer is `gcnShared` at the padded pair, so its guarantee is that one read back
  rw [GNN.gcnUncertain, ← GNN.gcnShared_exact W (P.padBack H.p) (H.padFront P.p) rfl]
  exact Set.image_congr' fun a => (GNN.aux_gcnUncertain_apply W P H a).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
