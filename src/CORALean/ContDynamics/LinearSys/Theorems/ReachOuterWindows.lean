module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachExact
public import CORALean.ContDynamics.LinearSys.Operations.Reach
public import CORALean.ContDynamics.LinearSys.Theorems.ExistsReachWindowExact
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalTimePointOuter
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# `reach` encloses `reachExact`, one window at a time

A time `t ∈ [0, tFinal]` falls in a window `τ_k` with `k < max 1 ⌈tFinal / Δt⌉`
(`exists_reach_window`), and `0 < tFinal` makes that `k < ⌈tFinal / Δt⌉`, a window
`reach` keeps; `timeInterval_timePoint_outer` puts `e^{At} x₀` in its set, off the
time-point set `timePoint Δt X₀ k` the window's own recursion runs on. The
order is the caller's, `η` itself rather than `m + 2`, admissible by `hε`,
since `reach` raises nothing itself: the statement is `reachWrappingFree_outer`'s
with that side condition and `0 < tFinal` added. [1, Alg. 1]'s soundness, at a
point matrix with no input.

## Inputs
* `sys` – linear system
* `params` – reach parameters
* `options` – step options

## Hypotheses
* `htFinal` – start time before final time
* `hΔt` – step length positive
* `hη` – order at least two
* `hε` – scaled norm small enough for the Taylor order

## Conclusion
* the exact reach lies in the window sets

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet ContSetLike Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {ContSet : ℕ → Type} [∀ n, ContSetLike (ContSet n) (Vec ℝ n)]
variable [∀ n, Plus (ContSet n) (Vec ℝ n)] [∀ n, LinComb (ContSet n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) ContSet] [Mtimes ℐ ContSet]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of the initial set under the flow, at every `t ∈ [0, tFinal - tStart]`,
is in one of `reach`'s windows. -/
theorem LinearSys.reach_outer (sys : LinearSys 𝕋 n) {params : Reach.Params (ContSet n) ℝ}
    {options : LinearSys.ReachOptions ℝ} (htFinal : params.tStart < params.tFinal)
    (hΔt : 0 < options.Δt) (hη : 2 ≤ options.η)
    (hε : ‖options.Δt • toRealMat sys.A‖ / ((options.η : ℝ) + 2) < 1) : -- --- CONCL ---
    sys.reachExact (params.tFinal - params.tStart) (toSet params.X₀)
      ⊆ toSet (sys.reach params options) := by -- --- PROOF ---
  unfold LinearSys.reach
  have htFinal := sub_pos.mpr htFinal
  obtain ⟨X₀, tStart, tF⟩ := params
  obtain ⟨Δt, η⟩ := options
  dsimp only at *
  generalize tF - tStart = tFinal at *
  intro y hy
  obtain ⟨t, ht, x₀, hx₀, rfl⟩ := Set.mem_iUnion₂.mp hy
  obtain ⟨k, hk, hkt, htk⟩ := LinearSys.exists_reach_window hΔt ht
  -- `0 < tFinal` keeps at least one window, so `max 1` changes nothing
  have hN : 1 ≤ ⌈tFinal / Δt⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr
    (div_pos htFinal hΔt)).ne'
  rw [max_eq_right hN] at hk
  -- window `k` holds `e^{At} x₀`, and `k < N`
  exact SetUnion.mem_toSet_range hk
    (sys.timeInterval_timePoint_outer hΔt hη hε X₀ hkt htk (Set.mem_image_of_mem _ hx₀))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
