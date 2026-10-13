module

public import CORALean.NN.Operations.EncloseReduceAt
public import CORALean.NN.Operations.RefinableNetworkEval

@[expose] public section

/-!
# The refinement loop's network evaluation encloses the network

[1, Alg. 3] lines 3-8: `encloseReduceAt` holds the network's output at every point of the
input set, at every order pattern and every reduction order — each reduction encloses its
input ([1, Prop. 2.13]) and each layer's enclosure its image ([1, Prop. 2.14]).

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem RefinableNetwork.encloseReduceAt_outer (ρ : ℕ) :
    ∀ {n m : ℕ} (rn : RefinableNetwork S n m) (ψ : Schedule) (X : S n) (x : Vec ℝ n),
      x ∈ construct X → rn.eval x ∈ construct (rn.encloseReduceAt ρ ψ X)
  | _, _, .nil, _, _, _, hx => hx
  | _, _, .cons L rest, ψ, X, x, hx =>
    rest.encloseReduceAt_outer ρ (Schedule.tail ψ) _ (L.eval x)
      (L.enclose_outer _ _ x (Reduce.reduce_outer X ρ hx))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
