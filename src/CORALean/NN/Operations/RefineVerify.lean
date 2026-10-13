module

public import CORALean.NN.Operations.RefineVerifyFrom

@[expose] public section

/-!
# Automatic abstraction refinement, the whole loop

[1, Alg. 3]: at most `I` iterations from line 1's order pattern, every order `1`, each
computing the output enclosure `Y⁽ⁱ⁾` with every layer's input reduced to order `ρ` (lines
3-8), returning `VERIFIED` (`true`) once `Y⁽ⁱ⁾` misses the unsafe set (lines 10-11), and
otherwise refining the order pattern (lines 14-15) and going round again; `UNKNOWN` (`false`)
once the iterations run out (line 17).

The check `Y ∩ S = ∅` is the caller's `isDisjoint`, a test on the representation that
`refineVerify_sound` holds to its meaning; lines 14-15, computing the heuristic `σ` and raising
`ψ` where it is largest, are the caller's `refineStep` — `Def. 4.4`'s neuron-wise and
`Def. 4.6`'s layer-wise rules are `Schedule.refineWorstNeurons` and `Schedule.refineWorst`,
and which is used decides only where the next order goes, the result being sound at every
schedule.

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

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: `true` is `VERIFIED`, `false` is `UNKNOWN` after `I` iterations. -/
def RefinableNetwork.refineVerify (rn : RefinableNetwork S n m) (ρ : ℕ) (X : S n)
    (isDisjoint : S m → Bool) (refineStep : Schedule → Schedule) (I : ℕ) : Bool :=
  let ψ : Schedule := fun _ _ => 1                            -- 1: order pattern ψ ← 1
  rn.refineVerifyFrom ρ X isDisjoint refineStep ψ I           -- 2-17

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
