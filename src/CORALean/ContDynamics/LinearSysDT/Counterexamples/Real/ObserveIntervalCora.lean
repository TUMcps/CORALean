module

public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveInterval
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
public import CORALean.ContDynamics.LinearSysDT.Operations.Canonical
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# CORA's interval observer misses the initial state off the origin

CORA's `priv_observe_interval` (the observer `Hinf-G`) seeds the estimate with `x = center(R0)`
and the error set with `R_x = R0`, and returns `x + box(R_x) + R_wv`: at the initial time the
box of `R0` moved by its own center. [1, Alg. 1] prints the same lines 1-2 (`x̂_0 ← center(X_0)`,
`S_{x,0} ← X_0`). For `R0 = {1}` in `ℝ¹` that is `{2}`, which misses the initial state `1`; the
error set must start as `R0 - center(R0)`, which is the hypothesis `x_0 - center(R0) ∈ R0` that
`LinearSysDT.observeInterval_outer` carries. Read from the source, not run.

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `R0 = {1}`: the initial state is in `R0` and not in the observer's first box. -/
theorem LinearSysDT.observeInterval_cora_counterexample : -- --- STMT ---
    let sys : LinearSysDT ℝ 1 := LinearSysDT.canonical 0
    let R₀ : Zonotope (Vec ℝ 1) := Zonotope.ofPoint (fun _ => 1)
    (fun _ => 1 : Vec ℝ 1) ∈ R₀.construct ∧
      (fun _ => 1 : Vec ℝ 1) ∉ (sys.observeInterval (0 : Mat ℝ 1 1) R₀ R₀
        (Zonotope.ofPoint 0) (fun _ => 0) (fun _ => 0) 0).construct := by -- --- PROOF ---
  intro sys R₀
  refine ⟨Zonotope.mem_ofPoint _, fun h => ?_⟩
  -- the first box is `center + box(R0) = {2}`
  have h0 := (h 0).1
  simp [LinearSysDT.observeInterval, LinearSysDT.observeIntervalState, Interval.plus,
    Interval.point, Zonotope.interval, R₀, Zonotope.ofPoint] at h0
  rw [Entrywise.entry_vec, Entrywise.entry_vec, Pi.add_apply] at h0
  exact absurd (show (1 : ℝ) + 1 ≤ 1 from h0) (by norm_num)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
