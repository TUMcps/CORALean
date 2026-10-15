module

public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatSubsetClosedBall

@[expose] public section

/-!
# The interval matrix product in a ball, by the size of the bounds

`Zonotope.mtimesIntervalMat_subset_closedBall` bounds the product by the entries of the center and
the radius of the interval matrix. Both are at most `(|inf| + |sup|)/2` entrywise, so the sum
`s = Σ_{j,k} (|inf_{jk}| + |sup_{jk}|)` serves for both: the product lies in the sup norm ball of
radius `2 s Σ_j absBound_j(Z)`. This is the form in which [1, Prop. 4] lets `F` and `G` of
Eq. (18) vanish: `s → 0` when the bounds do.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.mtimesIntervalMat_subset_closedBall_infSup (IM : Interval (Mat ℝ m n))
    (Z : Zonotope (Vec ℝ n)) :
    (Zonotope.mtimesIntervalMat IM Z).construct ⊆ Metric.closedBall (0 : Vec ℝ m)
      (2 * (∑ i, ∑ j, (|IM.inf i j| + |IM.sup i j|)) * ∑ j, Z.absBound j) := by -- --- PROOF ---
  set s : ℝ := ∑ i, ∑ j, (|IM.inf i j| + |IM.sup i j|) with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hentry : ∀ i j, |IM.inf i j| + |IM.sup i j| ≤ s := fun i j =>
    (Finset.single_le_sum (f := fun j => |IM.inf i j| + |IM.sup i j|)
      (fun _ _ => by positivity) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, (|IM.inf i j| + |IM.sup i j|))
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i))
  -- the center and the radius of the interval matrix are each bounded by `s` entrywise
  have h := Zonotope.mtimesIntervalMat_subset_closedBall IM Z (ρc := s) (ρr := s) hs0 hs0
    (fun i j => by
      have hc : IM.center i j = (2:ℝ)⁻¹ * (IM.inf i j + IM.sup i j) := rfl
      rw [hc, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2⁻¹)]
      have := abs_add_le (IM.inf i j) (IM.sup i j)
      have := hentry i j
      nlinarith)
    (fun i j => by
      have hc : IM.radius i j = (2:ℝ)⁻¹ * (IM.sup i j - IM.inf i j) := rfl
      rw [hc, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2⁻¹)]
      have := abs_sub (IM.sup i j) (IM.inf i j)
      have := hentry i j
      nlinarith)
  have : s + s = 2 * s := by ring
  rwa [this] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
