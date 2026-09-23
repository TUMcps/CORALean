import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.NN.BucketTolerance

/-!
# [1, Alg. 1] need not end

One neuron whose bounds are the point `1`, the static bucket at `0` (ReLU's, [1, Eq. 5]), and
any `ρ < 1`: `δ_max` starts at `max(u_k) - min(l_k) = 0`, so line 3's tenfold growth leaves it
at `0`, where the bucket holds nothing, `n̂_k/n_k = 1 > ρ`, and line 6 loops again. No `fuel`
is enough, with `le` the exact order. So [1, Thm. 1]'s "for any reduction rate ρ" holds only
where [1, Alg. 1] returns, which is why `bucketTolerance` is an `Option`.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1] returns nothing, at any `fuel`, on a single neuron fixed at `1` against the
bucket at `0`, whenever `ρ < 1`. -/
theorem bucketTolerance_eq_none_of_point {tol ρ : ℝ} (hρ : ρ < 1) (fuel : ℕ) :
    bucketTolerance (fun a b => decide (a ≤ b)) tol fuel (.static [0])
      (Interval.point (fun _ => (1 : ℝ)) : Interval (Vec ℝ 1)) ρ = none := by -- --- PROOF ---
  -- the bounds are one point, so `δmax` starts at `0` and tenfold growth keeps it there
  have hδ : maxOver (Interval.point (fun _ => (1 : ℝ)) : Interval (Vec ℝ 1)).sup
      - minOver (Interval.point (fun _ => (1 : ℝ)) : Interval (Vec ℝ 1)).inf = 0 := by
    simp [maxOver, minOver, Interval.point]
  -- and at `δ = 0` the bucket at `0` holds nothing, so `n̂/n = 1 > ρ` every round
  have hgrow : ∀ k, growBucketTolerance (fun a b => decide (a ≤ b)) (.static [0])
      (Interval.point (fun _ => (1 : ℝ)) : Interval (Vec ℝ 1)) ρ 0 k = none := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have hB : initMergeBuckets (fun a b => decide (a ≤ b)) (.static [0])
          (Interval.point (fun _ => (1 : ℝ)) : Interval (Vec ℝ 1)) 0 = fun _ => false := by
        funext i
        simp [initMergeBuckets, staticMergeBuckets, inMergeBucket, Interval.point]
      have hcount : bucketed (fun _ : Fin 1 => false) = 0 := by simp [bucketed]
      rw [growBucketTolerance]
      simp only [mul_zero, hB, hcount]
      rw [if_neg (by norm_num; linarith)]
      exact ih
  simp only [bucketTolerance, hδ, hgrow]
end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
