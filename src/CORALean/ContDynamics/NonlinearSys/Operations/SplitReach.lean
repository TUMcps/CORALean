module

public import CORALean.ContSet.Zonotope.Real.Operations.Split

@[expose] public section

/-!
# `splitReach`, one time step of conservative linearization with splitting

[1, Fig. 1]: run the step from `R((k - 1) r)`; if its linearization error is not admissible,
"split `R((k - 1) r)` into two sets and repeat reachable set computation" on each. The step
itself — linearize, compute `R_lin`, bound `L` by Prop. 1, test `L ⊆ L̄` — is `step`, which
answers `none` when the test fails; which generator to split is `pick`, the paper's performance
index `ρ_j` being `Zonotope.splitRank`. `fuel` caps the depth of the splitting, and an exhausted
budget is a failure; `splitReach_outer` says every start in `R` is answered by one segment.

## Inputs
* `step` – step on a zonotope
* `pick` – generator to split

## Output
* the segments' answers, or none

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {β : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Fig. 1] at one time step: the step's answer from `R`, or the answers from the two
halves of `R` split along `pick R`, at most `fuel` splits deep. -/
noncomputable def NonlinearSys.splitReach (step : Real.Zonotope (Vec ℝ n) → Option β)
    (pick : (R : Real.Zonotope (Vec ℝ n)) → Option (Fin R.h)) :
    ℕ → Real.Zonotope (Vec ℝ n) → Option (List β)
  | 0, _ => none
  | fuel + 1, R =>
    match step R with
    | some S => some [S]
    | none =>
      match pick R with
      | none => none
      | some j =>
        let halves := R.split j
        match NonlinearSys.splitReach step pick fuel halves.fst,
          NonlinearSys.splitReach step pick fuel halves.snd with
        | some l₁, some l₂ => some (l₁ ++ l₂)
        | _, _ => none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
