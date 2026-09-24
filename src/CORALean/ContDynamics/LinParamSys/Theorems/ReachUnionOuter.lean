import CORALean.ContDynamics.LinParamSys.Definitions.ReachUnionExact
import CORALean.ContDynamics.LinParamSys.Operations.ReachUnion
import CORALean.ContDynamics.LinParamSys.Theorems.ReachOrderAdmissible
import CORALean.ContDynamics.LinParamSys.Theorems.ReachStepkOuter
import CORALean.ContDynamics.LinearSys.Theorems.ExistsReachWindow
import CORALean.ContSet.SetUnion.SetUnion

/-!
# `reachUnion` encloses `reachUnionExact`, one window at a time

A time `t ∈ [0, tFinal]` falls in a window `τ_k` `reachUnion` keeps
(`LinearSys.exists_reach_window`), and `reachStepk_outer` puts `e^{At} x₀` in
that window's set, at whichever member `A` the run fixed. The order is
`reachUnion`'s own, admissible by `reachOrder_admissible` and the raise:
[1, Alg. 4]'s soundness at `U = {0}`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   24-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of `X₀` under every member's flow, at every time of `[0, p.tFinal]`,
is in one of `reachUnion`'s windows. -/
theorem LinParamSys.reachUnion_outer (sys : LinParamSys ℐ n) (p : LinearSys.ReachParams)
    (X₀ : S n) :
    sys.reachUnionExact p (construct X₀) ⊆ construct (sys.reachUnion p X₀) := by -- --- PROOF ---
  rintro _ ⟨A, hA, t, ht, x₀, hx₀, rfl⟩
  obtain ⟨k, hk, hkt, htk⟩ := LinearSys.exists_reach_window p.hΔt ht
  -- the order `reachUnion` runs at, `m + 2` in `reachStepk_outer`'s naming
  obtain ⟨m, hm⟩ : ∃ m, max p.η (sys.reachOrder p.Δt + 2) = m + 2 :=
    ⟨max p.η (sys.reachOrder p.Δt + 2) - 2, by omega⟩
  have hε : ‖(Interval.smul p.Δt sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 := by
    have hadm := sys.reachOrder_admissible p.Δt
    have hle : ((sys.reachOrder p.Δt + 2 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
      exact_mod_cast hm ▸ le_max_right _ _
    exact lt_of_le_of_lt (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (by linarith)) hadm
  -- window `k` is `e^{[A] t_k} H^R(τ_0)`, and `k < N`
  refine SetUnion.mem_construct.mpr ⟨sys.reachStepk p.Δt (m + 2) X₀ k, ?_, ?_⟩
  · rw [← hm]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  · exact sys.reachStepk_outer p.hΔt hε X₀ hA hkt htk (Set.mem_image_of_mem _ hx₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
