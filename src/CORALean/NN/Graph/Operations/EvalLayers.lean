module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# The graph part of a network, layer by layer, at one matrix

The exact network behind [1, Alg. 1]'s lines 3 to 6: `L` graph convolutions, step `s`
`H ↦ σₛ (Pm H Wₛ)` with the activation applied entrywise, the feature width `c s` changing from
step to step. `GNN.evalSteps` is the case of one width and the identity activation.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `L` convolutions with activations at a fixed matrix `Pm`, from width `c 0` to `c L`. -/
def GNN.evalLayers (Pm : Mat ℝ N N) :
    ∀ (L : ℕ) (c : ℕ → ℕ) (_ : ℕ → ℝ → ℝ) (_ : ∀ s, Mat ℝ (c s) (c (s + 1))),
      Mat ℝ N (c 0) → Mat ℝ N (c L)
  | 0, _, _, _, H => H
  | L + 1, c, σ, W, H =>
    GNN.evalLayers Pm L (fun s => c (s + 1)) (fun s => σ (s + 1)) (fun s => W (s + 1))
      ((Pm * H * W 0).map (σ 0))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
