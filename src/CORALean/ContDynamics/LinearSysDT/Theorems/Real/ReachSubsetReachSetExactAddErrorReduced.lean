module

public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachErrorReducedContainsReachError
public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ReachSubsetReachSetExactAddError

@[expose] public section

/-!
# The computed run stays inside the exact set plus the *reduced* error

`reach_subset_reachSetExact_add_error` with the error enlarged, which is the whole argument: the
error sits on the right of that inclusion, added to `reachSetExact`, so replacing it by anything
containing it keeps the inclusion true. Enlarging a computed set usually breaks a guarantee; here
it cannot, and that asymmetry is what lets the error be reduced at all. No induction of its own —
the induction is `reachErrorReduced_contains_reachError`'s — and no new hypothesis on the system.
What it costs is precision downstream: `reachInnerReduced` is a smaller set than `reachInner`.

## Inputs
* `sys` – system
* `o` – maximum zonotope order
* `R₀` – initial zonotope
* `U` – input zonotope
* `k` – step

## Hypotheses
* `ho` – order positive

## Conclusion
* the computed run lies in the exact set plus the reduced error
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- What a run computes stays inside the exact reachable set widened by the
reduced error, the error being the side of the inclusion that may grow. -/
theorem LinearSysDT.reach_subset_reachSetExact_add_errorReduced (sys : LinearSysDT ℝ n) {o : ℕ}
    (ho : 0 < o) (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct ⊆
      sys.reachSetExact (S := 𝒵) R₀ U k + (sys.reachErrorReduced ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct :=
  subset_trans (sys.reach_subset_reachSetExact_add_error ho R₀ U k)
    (Set.add_subset_add_left (sys.reachErrorReduced_contains_reachError ho R₀ U k))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
