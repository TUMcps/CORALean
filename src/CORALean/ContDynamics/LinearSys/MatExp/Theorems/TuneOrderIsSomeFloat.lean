import CORALean.ContDynamics.LinearSys.MatExp.Operations.TuneOrderFloat

/-!
# `tuneOrder` is complete in its fuel

If an order from `2` below `2 + fuel` passes the float test, the search of [1]'s order selector
returns one. Completeness is relative to the float test, not to the real predicate: the float
bound over-estimates the real one, so a real admissible order need not pass it.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Complete in its fuel: if an order in `[2, 2 + fuel)` passes the float test, the search
returns one. -/
theorem MatExp.tuneOrder_isSome {nrm ε : 𝕋} {fuel η : ℕ} (h2 : 2 ≤ η) (hη : η < 2 + fuel)
    (ht : MatExp.orderTest nrm ε η = true) :
    (MatExp.tuneOrder nrm ε fuel).isSome = true := by
  rw [MatExp.tuneOrder, List.find?_isSome]
  exact ⟨η, List.mem_map.mpr ⟨η - 2, List.mem_range.mpr (by omega), by omega⟩, ht⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
