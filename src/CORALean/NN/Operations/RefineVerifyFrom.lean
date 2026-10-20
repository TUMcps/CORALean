module

public import CORALean.NN.Operations.EncloseReduceAt

@[expose] public section

/-!
# The refinement loop from a given order pattern

[1, Alg. 3] lines 2-17 with `I` iterations left at order pattern `ψ`: the output enclosure
(lines 3-8, `encloseReduceAt`), `VERIFIED` (`true`) once it misses the unsafe set (lines
10-11), and otherwise a refinement step (lines 14-15) and the next iteration; `UNKNOWN`
(`false`) when none is left (line 17). The disjointness test and the refinement step are the
caller's; `RefineVerify` starts it at line 1's pattern.

## Inputs
* `rn` – refinable network
* `ρ` – order after reduction
* `X` – input set
* `isDisjoint` – test that the output set misses the unsafe set
* `refineStep` – refinement of the schedule

## Output
* verified if some remaining iteration's output misses the unsafe set, otherwise unknown

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

/-- Lines 2-17 from order pattern `ψ` with `I` iterations left. -/
def RefinableNetwork.refineVerifyFrom (rn : RefinableNetwork S n m) (ρ : ℕ) (X : S n)
    (isDisjoint : S m → Bool) (refineStep : Schedule → Schedule) : Schedule → ℕ → Bool
  | _, 0 => false                                             -- 17: return UNKNOWN
  | ψ, I + 1 =>
    let Y := rn.encloseReduceAt ρ ψ X                         -- 3-8: Y⁽ⁱ⁾ ← H⁽ⁱ⁾_κ
    if isDisjoint Y then true                                 -- 10-11: Y⁽ⁱ⁾ ∩ S = ∅, VERIFIED
    else rn.refineVerifyFrom ρ X isDisjoint refineStep        -- 14-15: σ, then raise ψ
      (refineStep ψ) I

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
