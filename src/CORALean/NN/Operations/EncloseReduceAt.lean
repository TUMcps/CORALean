module

public import CORALean.NN.Definitions.RefinableNetwork
public import CORALean.NN.Operations.Basic

@[expose] public section

/-!
# The network evaluation of the refinement loop

[1, Alg. 3] lines 3-8: from `H₀ = X`, each layer's input reduced to order `ρ` (line 5,
[1, Prop. 2.13]) and then enclosed at the layer's own order pattern (line 6, [1, Prop. 2.14]),
the last `H_κ` being `Y⁽ⁱ⁾`. `encloseAt` is the same without the reduction.

## Inputs
* `ρ` – order after reduction

## Output
* output set with every layer's input reduced first

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-8 at order pattern `ψ`, every layer's input reduced to order `ρ` first. -/
def RefinableNetwork.encloseReduceAt (ρ : ℕ) :
    ∀ {n m : ℕ}, RefinableNetwork S n m → Schedule → S n → S m
  | _, _, .nil, _, H => H                                            -- 8: Y⁽ⁱ⁾ ← H_κ
  | _, _, .cons L rest, ψ, H =>
    let H' := Reduce.reduce H ρ                                      -- 5: reduce(H_{k-1}, ρ)
    let Hk := L.enclose (Schedule.head ψ _) H'                       -- 6: enclose(L_k, H_{k-1})
    rest.encloseReduceAt ρ (Schedule.tail ψ) Hk

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
