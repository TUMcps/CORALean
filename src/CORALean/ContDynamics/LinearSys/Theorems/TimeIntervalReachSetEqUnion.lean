import CORALean.ContDynamics.LinearSys.Definitions.ReachSet
import CORALean.ContDynamics.LinearSys.Definitions.TimeIntervalReachSet

/-!
# The interval set is exactly the union [1, Def. 3.2] states

`timeIntervalReachSet` is written as one existential rather than as a literal
`Set.iUnion`, so it reads the same way `reachSet` does; this recovers the union
the thesis states it as, and is what lets a `reachSet`-indexed hypothesis — one
per time in `[0, r]`, as `ReachSetSubsetTimeIntervalInputSolution` supplies —
answer for the whole interval at once.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       11-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Def. 3.2]: the reachable set over `[0, r]` is the union of the
point-in-time reachable sets at every time in it. -/
theorem LinearSys.timeIntervalReachSet_eq_iUnion (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n)
    (r : ℝ) :
    sys.timeIntervalReachSet T R₀ U r
      = ⋃ t ∈ Set.Icc (0:ℝ) r, sys.reachSet T R₀ U t := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨x, u, traj, t, ht, rfl⟩
    exact Set.mem_biUnion ht ⟨x, u, traj, rfl⟩
  · intro hy
    obtain ⟨t, ht, x, u, traj, rfl⟩ := Set.mem_iUnion₂.mp hy
    exact ⟨x, u, traj, t, ht, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
