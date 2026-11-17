module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Basic

@[expose] public section

/-!
# `LinearSys.verifyTimeSetdiff`, the unverified times less a verified interval

CORA's `verifyTime/setdiff` removes a verified `[t₀, t₁]` from the closed intervals still to be
verified and drops every remainder shorter than a tolerance as a rounding error of the times. Here
the times are exact rationals and nothing is dropped: a remainder, however short, is a time not yet
verified (see `LinearSys.verifyTimeSetdiffCora_counterexample`). An interval disjoint from
`(t₀, t₁)` stays, the others keep their parts `[a, t₀]` and `[t₁, b]` that are nonempty.

## Inputs
* `U` – the unverified intervals
* `t₀` – start of the verified interval
* `t₁` – end of the verified interval

## Output
* the unverified intervals without `(t₀, t₁)`
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Each interval `[a, b]` meeting `(t₀, t₁)` is cut to `[a, t₀]` and `[t₁, b]` where nonempty. -/
def LinearSys.verifyTimeSetdiff (U : List (ℚ × ℚ)) (t₀ t₁ : ℚ) : List (ℚ × ℚ) :=
  U.flatMap fun iv =>
    if t₁ ≤ iv.1 ∨ iv.2 ≤ t₀ then [iv]                                   -- disjoint
    else (if iv.1 < t₀ then [(iv.1, t₀)] else []) ++ (if t₁ < iv.2 then [(t₁, iv.2)] else [])

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
