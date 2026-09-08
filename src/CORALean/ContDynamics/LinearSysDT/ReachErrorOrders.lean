import CORALean.ContDynamics.LinearSysDT.Operations
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBox

/-!
# What a run of `reachOrders` owes

`reachError` at a per-step order sequence: the same recursion, `reduceBox`
read at `o (k + 1)` — the order the sequence supplies for the step just
taken — in place of the one fixed `o` `reachError` reduces to throughout.

At `Zonotope` and at `𝕋 = ℝ`, for the reasons `reachError`'s own docstring
gives: `mtimes` is exact only there, and a zonotope rather than a `Set` is what
`minkDiffRep` can take as an operand.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `reachOrders` owes after `k` steps: every step's reduction box, read
at that step's own order, each carried forward by one `A` per step taken
since. -/
noncomputable def LinearSysDT.reachErrorOrders (sys : LinearSysDT ℝ n) (o : ℕ → ℕ)
    (ho : ∀ k, 0 < o k) (R₀ U : Zonotope (Vec ℝ n)) : ℕ → Zonotope (Vec ℝ n)
  | 0 => Zonotope.ofPoint 0
  | k + 1 => (Zonotope.mtimes sys.A (sys.reachErrorOrders o ho R₀ U k)).plus
      (Zonotope.reduceBox
        ((Zonotope.mtimes sys.A (sys.reachOrders (S := 𝒵) o ho R₀ U k)).plus U) (o (k + 1)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
