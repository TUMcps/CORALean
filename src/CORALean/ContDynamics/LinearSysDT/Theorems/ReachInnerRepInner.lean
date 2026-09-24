import CORALean.ContDynamics.LinearSysDT.Operations.ReachInnerRep
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachInnerInner
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffRepInner

/-!
# `reachInnerRep` is an inner approximation, as a representation

What `reachInner_inner` guarantees about a `Set`, carried to a zonotope a later
step could take as input: `minkDiffRep_inner` puts the returned zonotope inside
the Minkowski difference, and that difference *is* `reachInner`.

`M` is the caller's, and is the only thing left to choose. `minkDiffRep` checks
it — each error generator written in the run's own, and each row of the run
left non-negative room — and answers `none` where it does not check out, so a
wrong `M` costs precision and never soundness. The zonotope returned can be a
point, or `none` where the accumulated error has outgrown the run; neither is a
statement about the system, only about how much the reductions took.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Whatever `reachInnerRep` returns is inside the exact reachable set. -/
theorem LinearSysDT.reachInnerRep_inner (sys : LinearSysDT ℝ n) {o : ℕ} (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ)
    (M : Fin (sys.reach (S := 𝒵) o ho R₀ U k).h →
      Fin (sys.reachError o ho R₀ U k).h → ℝ) {D : Zonotope (Vec ℝ n)}
    (hD : sys.reachInnerRep o ho R₀ U k M = some D) :
    construct D ⊆ sys.reachSet (S := 𝒵) R₀ U k :=
  (Zonotope.minkDiffRep_inner _ _ M hD).trans (sys.reachInner_inner ho R₀ U k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
