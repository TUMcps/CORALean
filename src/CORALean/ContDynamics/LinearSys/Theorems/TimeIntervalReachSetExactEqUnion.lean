module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachSetExact
public import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalReachSetExact

@[expose] public section

/-!
# The interval set is exactly the union [1, Def. 3.2] states

`timeIntervalReachSetExact` is written as one existential rather than as a literal
`Set.iUnion`, so it reads the same way `reachSetExact` does; this recovers the union
the thesis states it as, and is what lets a `reachSetExact`-indexed hypothesis — one
per time in `[0, r]`, as `ReachSetExactSubsetTimeIntervalInputSolution` supplies —
answer for the whole interval at once.

## Inputs
* `sys` – linear system
* `T` – time domain
* `R₀` – initial set
* `U` – input set
* `r` – interval end

## Hypotheses
* none

## Conclusion
* the interval reach set is the union of the point-in-time reach sets

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Def. 3.2]: the reachable set over `[0, r]` is the union of the
point-in-time reachable sets at every time in it. -/
theorem LinearSys.timeIntervalReachSetExact_eq_iUnion (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n)
    (r : ℝ) :
    sys.timeIntervalReachSetExact T R₀ U r
      = ⋃ t ∈ Set.Icc (0:ℝ) r, sys.reachSetExact T R₀ U t := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨x, u, traj, t, ht, rfl⟩
    exact Set.mem_biUnion ht ⟨x, u, traj, rfl⟩
  · intro hy
    obtain ⟨t, ht, x, u, traj, rfl⟩ := Set.mem_iUnion₂.mp hy
    exact ⟨x, u, traj, t, ht, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
