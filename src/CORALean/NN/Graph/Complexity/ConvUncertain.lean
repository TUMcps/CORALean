import CORALean.NN.Graph.Operations.GcnShared
import CORALean.NN.Graph.Operations.GcnUncertain

/-!
# `GNN.gcnShared`'s and `GNN.gcnUncertain`'s counts

[1, Prop. 5]'s `O(h₁ h₂³)`: the layer at an uncertain graph is
[1, Lemma 1]'s multiplication followed by an affine map, so its dependent
generator count is `(P.h + 1) * (H.h + 1)` — the product [1, Lemma 1] predicts —
and one of the per-layer counts [1, Thm. 1]'s overall bound is assembled from —
and its independent block is empty, `bilin` being a claim about `point`. `rfl`
against the structure instances in `ConvUncertain.lean` and
`Operations/Bilin.lean`.

`gcnShared_p` is not here: a chain of steps rests on the factor set being kept,
so it sits beside the definition rather than in this table.

Padding moves the factor count and nothing else, which is why `gcnUncertain`
counts generators exactly as `gcnShared` does over `P.p + H.p` factors.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GNN.gcnShared_h (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) (hp : P.p = H.p) :
    (GNN.gcnShared W P H hp).h = (P.h + 1) * (H.h + 1) := rfl

theorem GNN.gcnShared_q (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) (hp : P.p = H.p) : (GNN.gcnShared W P H hp).q = 0 := rfl

theorem GNN.gcnUncertain_p (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) : (GNN.gcnUncertain W P H).p = P.p + H.p := rfl

theorem GNN.gcnUncertain_h (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) : (GNN.gcnUncertain W P H).h = (P.h + 1) * (H.h + 1) := rfl

theorem GNN.gcnUncertain_q (W : Mat ℝ F₁ F₂) (P : PolyZonotope (Mat ℝ N N))
    (H : PolyZonotope (Mat ℝ N F₁)) : (GNN.gcnUncertain W P H).q = 0 := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
