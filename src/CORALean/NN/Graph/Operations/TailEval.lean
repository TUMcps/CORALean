import CORALean.ContSet.ContSet.ContSet

/-!
# The layers after the global pooling, at one point

[1, Alg. 1], lines 11 to 14: the standard layers after the pooling, applied one after the other,
the width `d t` changing from layer to layer. `tailEnclose` is their enclosure on sets.

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

/-- The exact layers `g t`, one after the other, from width `d 0` to `d T`. -/
def GNN.tailEval : ∀ (T : ℕ) (d : ℕ → ℕ) (_ : ∀ t, Vec ℝ (d t) → Vec ℝ (d (t + 1))),
    Vec ℝ (d 0) → Vec ℝ (d T)
  | 0, _, _, x => x
  | T + 1, d, g, x => GNN.tailEval T (fun t => d (t + 1)) (fun t => g (t + 1)) (g 0 x)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
