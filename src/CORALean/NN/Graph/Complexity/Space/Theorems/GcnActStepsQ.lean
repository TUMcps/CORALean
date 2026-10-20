module

public import CORALean.NN.Graph.Operations.GcnActSteps

@[expose] public section

/-!
# `GNN.gcnActSteps` leaves no independent generators

[1, Alg. 1]: every step ends in `dependent`, so the independent generators an activation enclosure
adds are dependent ones by the time the next convolution, the pooling or the output sees the set;
a chain of no step returns its input.

## Inputs
* `L` – number of steps

## Hypotheses
* none

## Conclusion
* the chain's set has no independent generators if its input has none

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


-- =======================================  MAIN THEOREM  ======================================= --

/-- With a first set free of independent generators, the chain's set is too. -/
theorem GNN.gcnActSteps_q (L : ℕ) :
    ∀ (c : ℕ → ℕ) (W : ∀ s, Mat ℝ (c s) (c (s + 1))) (acts : ∀ s, GNN.ActLayer N (c (s + 1)))
      (P : PolyZonotope (Mat ℝ N N)) (H : PolyZonotope (Mat ℝ N (c 0))) (hp : P.p = H.p),
      H.q = 0 → (GNN.gcnActSteps L c W acts P H hp).q = 0 := by -- --- PROOF ---
  induction L with
  | zero => intro c W acts P H hp hq; exact hq
  | succ L ih =>
    intro c W acts P H hp hq
    exact ih _ _ _ _ _ _ rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
