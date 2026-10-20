module

public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntervalEstimateErrorEqHull
public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.LuenbergerErrorMemReachErrorSet
public import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Real.Theorems.MemPoint

@[expose] public section

/-!
# The reachability-based interval estimator holds the true state

[1, Thm. 2] through [1, Alg. 1]: every run of `x_{k+1} = A x_k + B u_k + E w_k`,
`y_k = C x_k + F v_k` with `x_0 ∈ X₀`, `w_k ∈ W`, `v_k ∈ V` lies in the box
`x̂_k + [e̲_k, e̅_k]` at every step, for any gain `L`. The estimate of the algorithm is the
observer [1, Eq. 10] from `x̂_0 = p₀`, its error lies in `Ω_k`
(`luenbergerError_mem_reachErrorSet`), and `Ω_k` in the error box
(`intervalEstimate_error_eq_hull`).

## Inputs
* `sys` – system
* `L` – observer gain
* `X₀` – initial zonotope
* `W` – disturbance zonotope
* `V` – noise zonotope
* `u` – inputs
* `y` – measurements
* `x` – true states
* `w` – true disturbances
* `v` – true noise
* `k` – step

## Hypotheses
* `h0` – start lies in `X₀`
* `hw` – disturbances lie in `W`
* `hv` – noise lies in `V`
* `hstep` – the dynamics hold
* `hy` – the measurements follow the outputs

## Conclusion
* the true state lies in the estimator's box

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n nu ny nw nv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.intervalEstimate_outer (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (X₀ : Zonotope (Vec ℝ n))
    (W : Zonotope (Vec ℝ sys.r)) (V : Zonotope (Vec ℝ sys.s)) (u : ℕ → Vec ℝ sys.m)
    (y : ℕ → Vec ℝ sys.q) (x : ℕ → Vec ℝ n) (w : ℕ → Vec ℝ sys.r) (v : ℕ → Vec ℝ sys.s)
    (h0 : x 0 ∈ X₀.construct) (hw : ∀ k, w k ∈ W.construct) (hv : ∀ k, v k ∈ V.construct)
    (hstep : ∀ k, x (k + 1) = sys.A *ᵥ x k + sys.B *ᵥ u k + sys.E *ᵥ w k)
    (hy : ∀ k, y k = sys.C *ᵥ x k + sys.F *ᵥ v k) (k : ℕ) : -- --- CONCL ---
    x k ∈ (LinearSysDT.intervalEstimate sys L X₀ W V u y k).construct := by -- --- PROOF ---
  set S := LinearSysDT.intervalEstimateState sys L X₀ W V u y
  -- the algorithm's estimate is the Luenberger observer from `p₀`
  have he := LinearSysDT.luenbergerError_mem_reachErrorSet sys L X₀ W V u y x
    (fun k => (S k).x) w v h0 hw hv hstep hy rfl (fun k => rfl) k
  have hbox := (LinearSysDT.intervalEstimate_error_eq_hull sys L X₀ W V u y k).1 he
  have hx : x k = (S k).x + (x k - (S k).x) := by abel
  rw [hx]
  exact Interval.plus_outer _ _ ⟨_, Interval.mem_point _, _, hbox, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
