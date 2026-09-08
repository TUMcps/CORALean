import CORALean.ContDynamics.LinearSysDT.Theorems.ReachErrorReducedContainsReachError
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSubsetReachSetAddError

/-!
# The computed run stays inside the exact set plus the *reduced* error

`reach_subset_reachSet_add_error` with the error enlarged, which is the whole
argument: the error sits on the right of that inclusion, added to `reachSet`,
so replacing it by anything containing it keeps the inclusion true. Enlarging
a computed set usually breaks a guarantee; here it cannot, and that asymmetry
is what lets the error be reduced at all.

So no induction of its own — the induction is
`reachErrorReduced_contains_reachError`'s — and no new hypothesis on the
system. What it costs is precision downstream: `reachInnerReduced` is a
smaller set than `reachInner`, by exactly this widening.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- What a run computes stays inside the exact reachable set widened by the
reduced error, the error being the side of the inclusion that may grow. -/
theorem LinearSysDT.reach_subset_reachSet_add_errorReduced (sys : LinearSysDT ℝ n) {o : ℕ}
    (ho : 0 < o) (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) :
    (sys.reach (S := 𝒵) o ho R₀ U k).construct ⊆
      sys.reachSet (S := 𝒵) R₀ U k + (sys.reachErrorReduced o ho R₀ U k).construct :=
  subset_trans (sys.reach_subset_reachSet_add_error ho R₀ U k)
    (Set.add_subset_add_left (sys.reachErrorReduced_contains_reachError ho R₀ U k))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
