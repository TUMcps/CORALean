module

public import CORALean.NN.Operations.RefineVerifyFrom

@[expose] public section

/-!
# Automatic abstraction refinement, the whole loop

[1, Alg. 3]: at most `I` iterations from line 1's order pattern, every order `1`, each computing the
output enclosure `Y⁽ⁱ⁾` with every layer's input reduced to order `ρ` (lines 3-8), returning
`VERIFIED` (`true`) once `Y⁽ⁱ⁾` misses the unsafe set (lines 10-11), and otherwise refining the
order pattern (lines 14-15); `UNKNOWN` (`false`) once the iterations run out (line 17). The check `Y
∩ S = ∅` is the caller's `isDisjoint`, which `refineVerify_sound` holds to its meaning; lines 14-15
are the caller's `refineStep` — `Def. 4.4`'s and `Def. 4.6`'s rules are
`Schedule.refineWorstNeurons` and `Schedule.refineWorst` — and decide only where the next order
goes, the result being sound at every schedule.

## Inputs
* `rn` – refinable network
* `ρ` – order after reduction
* `X` – input set
* `isDisjoint` – test that the output set misses the unsafe set
* `refineStep` – refinement of the schedule
* `I` – maximal number of iterations

## Output
* verified if some iteration's output misses the unsafe set, otherwise unknown

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../references/2023/ladner-hscc-abstraction-refinement.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: `true` is `VERIFIED`, `false` is `UNKNOWN` after `I` iterations. -/
def RefinableNetwork.refineVerify (rn : RefinableNetwork S n m) (ρ : ℕ) (X : S n)
    (isDisjoint : S m → Bool) (refineStep : Schedule → Schedule) (I : ℕ) : Bool :=
  -- 1. `Initialize order pattern ψ ← 1`
  let ψ : Schedule := fun _ _ => 1
  -- 2. `for i = 1, …, I`: lines 3-15 each; 17. `return UNKNOWN` once they are spent
  rn.refineVerifyFrom ρ X isDisjoint refineStep ψ I

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
