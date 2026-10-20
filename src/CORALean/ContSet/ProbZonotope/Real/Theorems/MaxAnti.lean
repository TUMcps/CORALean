module

public import CORALean.ContSet.ProbZonotope.Real.Operations.Max

@[expose] public section

/-!
# `ProbZonotope.max` falls with `m`

The density on the `m`-sigma bound, `K exp(-m²/2)` with `K ≥ 0`, is smaller on a larger bound:
`0 ≤ m ≤ m'` gives `max(probZ, m') ≤ max(probZ, m)`. It is what makes the density steps of
`pyramid` between consecutive layers non-negative.

## Inputs
* `P` – probabilistic zonotope
* `m` – real number
* `m'` – real number

## Hypotheses
* `hd` – `0 ≤ P.cov.det`
* `h0` – `0 ≤ m`
* `h` – `m ≤ m'`

## Conclusion
* `max` is antitone in `m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open scoped _root_.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.max_anti (P : ProbZonotope n) (hd : 0 ≤ P.cov.det) {m m' : ℝ}
    (h0 : 0 ≤ m) (h : m ≤ m') : -- --- CONCL ---
    P.max m' ≤ P.max m := by -- --- PROOF ---
  unfold ProbZonotope.max
  have hK : 0 ≤ 1 / ((2 * π) ^ ((n : ℝ) / 2) * P.cov.det ^ ((1 : ℝ) / 2)) := by
    have : 0 < 2 * π := by positivity
    positivity
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK
  nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
