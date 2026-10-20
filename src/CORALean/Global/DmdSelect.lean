module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The best rank of the dynamic mode decomposition

The loop of `priv_identifyDMD`: for `rank = 1, …, rankMax` build the candidate system,
`err = computeError(traj, sysTemp)`, and keep it if `err < errBest`. `computeError` is
`err`, the comparison `lt`; both are arguments. `errBest = inf` at the start is `none`
here, which takes the first candidate whatever its error, as `err < inf` does for every
finite error.
The source is [1].

## Inputs
* `lt` – strict comparison of errors
* `err` – error of a candidate
* `cand` – candidate for each rank
* `rankMax` – largest rank

## Output
* the first least-error candidate, none when no rank is tried

## References

* [1] `contDynamics/@linearSysDT/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The candidate of the first rank with the least error, `none` for `rankMax = 0`. -/
def dmdSelect (lt : ℝ → ℝ → Bool) (err : α → ℝ) (cand : ℕ → α) (rankMax : ℕ) : Option α :=
  ((List.range rankMax).foldl (fun best i =>
    let sysTemp := cand (i + 1)                                      -- rank = i + 1
    let errTemp := err sysTemp                                       -- computeError(traj,sysTemp)
    match best with
    | none => some (sysTemp, errTemp)
    | some (_, errBest) => if lt errTemp errBest then some (sysTemp, errTemp) else best) none).map
      Prod.fst

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
