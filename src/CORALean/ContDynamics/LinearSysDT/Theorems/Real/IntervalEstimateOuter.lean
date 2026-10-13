import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntervalEstimateErrorEqHull
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.LuenbergerErrorMemReachErrorSet
import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
import CORALean.ContSet.Interval.Real.Theorems.MemPoint

/-!
# The reachability-based interval estimator holds the true state

[1, Thm. 2] through [1, Alg. 1]: every run of `x_{k+1} = A x_k + B u_k + E w_k`,
`y_k = C x_k + F v_k` with `x_0 ∈ X₀`, `w_k ∈ W`, `v_k ∈ V` lies in the box
`x̂_k + [e̲_k, e̅_k]` at every step, for any gain `L`. The estimate of the algorithm is the
observer [1, Eq. 10] from `x̂_0 = p₀`, its error lies in `Ω_k`
(`luenbergerError_mem_reachErrorSet`), and `Ω_k` in the error box
(`intervalEstimate_error_eq_hull`).

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n nu ny nw nv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.intervalEstimate_outer (A : Mat ℝ n n) (B : Mat ℝ n nu) (C : Mat ℝ ny n)
    (E : Mat ℝ n nw) (F : Mat ℝ ny nv) (L : Mat ℝ n ny) (X₀ : Zonotope (Vec ℝ n))
    (W : Zonotope (Vec ℝ nw)) (V : Zonotope (Vec ℝ nv)) (u : ℕ → Vec ℝ nu)
    (y : ℕ → Vec ℝ ny) (x : ℕ → Vec ℝ n) (w : ℕ → Vec ℝ nw) (v : ℕ → Vec ℝ nv)
    (h0 : x 0 ∈ X₀.construct) (hw : ∀ k, w k ∈ W.construct) (hv : ∀ k, v k ∈ V.construct)
    (hstep : ∀ k, x (k + 1) = A *ᵥ x k + B *ᵥ u k + E *ᵥ w k)
    (hy : ∀ k, y k = C *ᵥ x k + F *ᵥ v k) (k : ℕ) :
    x k ∈ (LinearSysDT.intervalEstimate A B C E F L X₀ W V u y k).construct := by -- --- PROOF ---
  set S := LinearSysDT.intervalEstimateState A B C E F L X₀ W V u y
  -- the algorithm's estimate is the Luenberger observer from `p₀`
  have he := LinearSysDT.luenbergerError_mem_reachErrorSet A B C E F L X₀ W V u y x
    (fun k => (S k).x) w v h0 hw hv hstep hy rfl (fun k => rfl) k
  have hbox := (LinearSysDT.intervalEstimate_error_eq_hull A B C E F L X₀ W V u y k).1 he
  have hx : x k = (S k).x + (x k - (S k).x) := by abel
  rw [hx]
  exact Interval.plus_outer _ _ ⟨_, Interval.mem_point _, _, hbox, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
