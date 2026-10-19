module

public import CORALean.NN.Graph.Operations.TailEnclose
public import CORALean.NN.Graph.Operations.TailEval

@[expose] public section

/-!
# The enclosed tail contains the exact one

[1, Thm. 1], soundness, and [1, Alg. 1], lines 11 to 14: if each enclosure `f t` contains the image
of the layer `g t` it encloses, the chain of enclosures contains the chain of layers, from a point
of the set it starts at: an enclosure composes with an enclosure.

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


-- =======================================  MAIN THEOREM  ======================================= --

/-- Enclosing layer by layer encloses the composition. -/
theorem GNN.tailEval_mem_tailEnclose (T : ℕ) : -- --- CONCL ---
    ∀ (d : ℕ → ℕ) (g : ∀ t, Vec ℝ (d t) → Vec ℝ (d (t + 1)))
      (f : ∀ t, PolyZonotope (Vec ℝ (d t)) → PolyZonotope (Vec ℝ (d (t + 1))))
      (_ : ∀ t S x, x ∈ S.construct → g t x ∈ (f t S).construct)
      (S : PolyZonotope (Vec ℝ (d 0))) (x : Vec ℝ (d 0)),
      x ∈ S.construct →
        GNN.tailEval T d g x ∈ (GNN.tailEnclose T d f S).construct := by -- --- PROOF ---
  induction T with
  | zero => intro d g f hf S x hx; exact hx
  | succ T ih =>
    intro d g f hf S x hx
    exact ih (fun t => d (t + 1)) (fun t => g (t + 1)) (fun t => f (t + 1))
      (fun t => hf (t + 1)) (f 0 S) (g 0 x) (hf 0 S x hx)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
