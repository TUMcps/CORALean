module

public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.NN.Operations.BucketTolerance

@[expose] public section

/-!
# [1, Alg. 1] need not end

ℝ-only, since it rests on `δmax` starting at exactly `0`: a scalar that steps every result
outward, as the native binary64 model does, starts it above `0` and may well return.

One neuron whose bounds are the point `1`, the static bucket at `0` (ReLU's, [1, Eq. 5]), and
any `ρ < 1`: `δ_max` starts at `max(u_k) - min(l_k) = 0`, so line 3's tenfold growth leaves it
at `0`, where the bucket holds nothing, `n̂_k/n_k = 1 > ρ`, and line 6 loops again. No `fuel`
is enough, with `le` the exact order. So [1, Thm. 1]'s "for any reduction rate ρ" holds only
where [1, Alg. 1] returns, which is why `bucketTolerance` is an `Option`.

## Inputs
* `tol` – tolerance on the remaining fraction
* `ρ` – reduction rate
* `fuel` – bound on the loop iterations

## Hypotheses
* `hρ` – rate is below one

## Conclusion
* the algorithm returns nothing at any fuel on a single fixed neuron

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Float Float.FloatOps


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1] returns nothing, at any `fuel`, on a single neuron fixed at `1` against the
bucket at `0`, whenever `ρ < 1`. -/
theorem bucketTolerance_eq_none_of_point {tol ρ : ℝ} (hρ : ρ < 1) (fuel : ℕ) :
    bucketTolerance (fun a b => decide (a ≤ b)) tol fuel (.static [0])
      (Float.Interval.point (fun _ => (1 : ℝ)) : Float.Interval (Vec ℝ 1)) ρ
      = none := by -- --- PROOF ---
  -- the bounds are one point, so `δmax` starts at `0` and tenfold growth keeps it there
  have hδ : subUp (maxOver (Float.Interval.point (fun _ => (1 : ℝ)) : Float.Interval (Vec ℝ 1)).sup)
      (minOver (Float.Interval.point (fun _ => (1 : ℝ)) : Float.Interval (Vec ℝ 1)).inf) = 0 := by
    simp only [maxOver, minOver, Fin.foldl_succ, Fin.foldl_zero]
    show max (1 : ℝ) 1 + -min 1 1 = 0
    norm_num
  have hten : ∀ k, nsmulUp k (0 : ℝ) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => show (0 : ℝ) + nsmulUp k 0 = 0; rw [ih, add_zero]
  -- at `δ = 0` the bucket at `0` holds nothing, so `n̂/n = 1 > ρ` every round
  have hB : initMergeBuckets (fun a b => decide (a ≤ b)) (.static [0])
      (Float.Interval.point (fun _ => (1 : ℝ)) : Float.Interval (Vec ℝ 1)) 0 = fun _ => false := by
    funext i
    show (decide ((0 : ℝ) + -0 ≤ 1) && decide ((1 : ℝ) ≤ 0 + 0) || false) = false
    norm_num
  have hratio : ratio (𝕋 := ℝ) (1 - bucketed (fun _ : Fin 1 => false)) 1 = 1 := by
    have hcount : bucketed (fun _ : Fin 1 => false) = 0 := by simp [bucketed]
    rw [hcount]
    show (1 + 0 : ℝ) / (1 + 0) = 1
    norm_num
  -- so every round of the growth phase finds the same nothing, and so does its last
  have hgrow : ∀ k, growBucketTolerance (fun a b => decide (a ≤ b)) (.static [0])
      (Float.Interval.point (fun _ => (1 : ℝ)) : Float.Interval (Vec ℝ 1)) ρ 0 k = none := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [growBucketTolerance]
      simp only [hten, hB, hratio]
      rw [if_neg (by simp; linarith)]
      exact ih
  simp only [bucketTolerance, hδ, hgrow]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
