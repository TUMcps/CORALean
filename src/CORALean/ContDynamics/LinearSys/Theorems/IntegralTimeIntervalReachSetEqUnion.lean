import CORALean.ContDynamics.LinearSys.Definitions.IntegralReachSet
import CORALean.ContDynamics.LinearSys.Definitions.IntegralTimeIntervalReachSet

/-!
# The integral interval set is exactly the union [1, Def. 3.2] states

`integralTimeIntervalReachSet` is written as one existential rather than as a
literal `Set.iUnion`, so it reads the same way `integralReachSet` does; this
recovers the union the thesis states it as. One `T` covers every `t`, the same
way `timeIntervalReachSet_eq_iUnion` does — a single `IntegralTrajectory` is
what supplies every `x t` at once, so nothing here needs `T` to vary with `t`
the way `integralReachSet_eq`'s own `T := Set.Icc 0 t` does.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       16-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Def. 3.2]: the integral-equation reachable set over `[0, r]` is the
union of the point-in-time integral reachable sets at every time in it. -/
theorem LinearSys.integralTimeIntervalReachSet_eq_iUnion (sys : LinearSys 𝕋 n) (T : Set ℝ)
    (R₀ U : S n) (r : ℝ) :
    sys.integralTimeIntervalReachSet T R₀ U r
      = ⋃ t ∈ Set.Icc (0:ℝ) r, sys.integralReachSet T R₀ U t := by -- --- PROOF ---
  ext y
  constructor
  · rintro ⟨x, u, traj, t, ht, rfl⟩
    exact Set.mem_biUnion ht ⟨x, u, traj, rfl⟩
  · intro hy
    obtain ⟨t, ht, x, u, traj, rfl⟩ := Set.mem_iUnion₂.mp hy
    exact ⟨x, u, traj, t, ht, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
