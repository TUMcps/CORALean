module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# A chain of message-passing steps with a layer after each, at one matrix

[1, Sec. 4.3]'s network with its activations: `L` message-passing steps at a fixed matrix `Pm`,
each followed by a layer `g` that acts on every node alone, a node's feature row going in and
coming out. A graph convolution with its activation is `g x = σ (x W)` (`σ` elementwise), and a
node-level output may carry further layers of the same kind. `GNN.evalSteps` is the case
`g x = x W`, which has no activation.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `L` message-passing steps at a fixed matrix `Pm`, the per-node layer `g i` after step `i`. -/
def GNN.evalStepsLayers {N F : ℕ} (Pm : Mat ℝ N N) :
    ∀ (L : ℕ), (Fin L → Vec ℝ F → Vec ℝ F) → Mat ℝ N F → Mat ℝ N F
  | 0, _, h => h
  | L + 1, g, h =>
    GNN.evalStepsLayers Pm L (fun i => g i.succ) (Matrix.of fun u => g 0 ((Pm * h) u))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
