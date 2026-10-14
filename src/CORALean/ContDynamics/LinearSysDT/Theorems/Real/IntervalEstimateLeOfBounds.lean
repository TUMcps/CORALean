module

public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntervalEstimateErrorEqHull

@[expose] public section

/-!
# The reachability-based estimator is the tightest box around the reachable error

A consequence of Eq. 26 of [1, Thm. 2]: any bounds `lo ≤ e ≤ hi` holding on all of `Ω_k` hold
on the error box of [1, Alg. 1], so `x̂_k + lo ≤ x̲_k` and `x̅_k ≤ x̂_k + hi`. This is the step
the comparisons [1, Thm. 6], [1, Thm. 7] and [1, Thm. 8] end with (their Eqs. 54, 63 and 80):
another method bounds the reachable error, and the box is the hull of it.

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

open Matrix Pointwise CORALean.Real

variable {n nu ny nw nv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.intervalEstimate_le_of_bounds (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (X₀ : Zonotope (Vec ℝ n)) (W : Zonotope (Vec ℝ sys.r)) (V : Zonotope (Vec ℝ sys.s))
    (u : ℕ → Vec ℝ sys.m) (y : ℕ → Vec ℝ sys.q) (k : ℕ) (lo hi : Vec ℝ n)
    (h : ∀ e ∈ LinearSysDT.reachErrorSet sys L X₀ W V k, ∀ i, lo i ≤ e i ∧ e i ≤ hi i)
    (i : Fin n) :
    let x := (LinearSysDT.intervalEstimateState sys L X₀ W V u y k).x
    x i + lo i ≤ (LinearSysDT.intervalEstimate sys L X₀ W V u y k).inf i ∧
      (LinearSysDT.intervalEstimate sys L X₀ W V u y k).sup i ≤
        x i + hi i := by -- --- PROOF ---
  intro x
  obtain ⟨-, heq⟩ := LinearSysDT.intervalEstimate_error_eq_hull sys L X₀ W V u y k
  set s := LinearSysDT.intervalEstimateState sys L X₀ W V u y k
  set Ω := LinearSysDT.reachErrorSet sys L X₀ W V k
  -- `Ω_k` is nonempty: the centres of `⟨0, H₀⟩`, `W` and `V`
  have hne : Ω.Nonempty := by
    refine ⟨_, Set.add_mem_add (Set.add_mem_add ⟨0, ⟨0, by simp, by simp⟩, rfl⟩
      (Set.finsetSum_mem_finsetSum _ _ _ fun j _ => ⟨W.c, ⟨0, by simp, by simp⟩, rfl⟩))
      (Set.finsetSum_mem_finsetSum _ _ _ fun j _ => ⟨V.c, ⟨0, by simp, by simp⟩, rfl⟩)⟩
  -- the error box is the hull, whose bounds `lo` and `hi` bound
  have hlo : lo i ≤ (s.Sx.interval.plus (s.Sw.plus s.Sv)).inf i := by
    rw [heq]
    exact le_csInf (hne.image _) (by rintro _ ⟨e, he, rfl⟩; exact (h e he i).1)
  have hhi : (s.Sx.interval.plus (s.Sw.plus s.Sv)).sup i ≤ hi i := by
    rw [heq]
    exact csSup_le (hne.image _) (by rintro _ ⟨e, he, rfl⟩; exact (h e he i).2)
  exact ⟨by show x i + lo i ≤ x i + _; linarith, by show x i + _ ≤ x i + hi i; linarith⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
