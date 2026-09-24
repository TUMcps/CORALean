import CORALean.NN.Graph.Operations.Ball

/-!
# The ball, enumerated

`Finset.orderEmbOfFin` turns `ball A v L : Finset (Fin N)` into a plain function
`Fin (ball A v L).card → Fin N`: an `OrderEmbedding`, so injectivity comes free
(`RelEmbedding.injective`), and its range is the ball itself
(`Finset.range_orderEmbOfFin`), which is the membership fact `evalSteps_row_ball`'s
`κ` needs. This is *an* enumeration of `[1, §4.3]`'s ball, not an efficient way to find
one — see `Theorems/EvalStepsRowBallEnum.lean` for why that distinction matters here.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ball A v L`, enumerated by its own order: `Finset.orderEmbOfFin` at the ball's
own cardinality, coerced to a plain function into `Fin N`. -/
noncomputable def GNN.ballEnum (A : Mat ℝ N N) (v : Fin N) (L : ℕ) :
    Fin (GNN.ball A v L).card → Fin N :=
  (GNN.ball A v L).orderEmbOfFin rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
