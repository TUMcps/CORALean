import CORALean.NN.BucketTolerance

/-!
# What [1, Alg. 1] returns meets the reduction rate

Line 16 is the only exit of the bisection, so the buckets returned are ones the test there
passed at: the fraction of neurons they leave is within `tol` of `ρ`. That is all [1, Alg. 1]
promises. It says nothing of which neurons merge, and needs not: Prop. 4 is sound at every
bucket, so nothing here is a soundness hypothesis. `le` need only be sound on a `true`.

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

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1]: the buckets returned leave `n̂_k` neurons with `|n̂_k/n_k - ρ| ≤ tol`. -/
theorem bucketTolerance_approx {le : ℝ → ℝ → Bool} (hle : ∀ a b, le a b = true → a ≤ b)
    {tol : ℝ} {fuel : ℕ} {B : MergeBuckets ℝ} {I_k : Interval (Vec ℝ n)} {ρ : ℝ}
    {B_kδ : Fin n → Bool} (h : bucketTolerance le tol fuel B I_k ρ = some B_kδ) :
    |((n - bucketed B_kδ : ℕ) : ℝ) / n - ρ| ≤ tol := by -- --- PROOF ---
  -- the bisection returns only where line 16's test passed, at every fuel
  have key : ∀ (k : ℕ) (δmin δmax : ℝ),
      bisectBucketTolerance le tol B I_k ρ δmin δmax k = some B_kδ →
        |((n - bucketed B_kδ : ℕ) : ℝ) / n - ρ| ≤ tol := by
    intro k
    induction k with
    | zero => intro _ _ h0; exact absurd h0 (by simp [bisectBucketTolerance])
    | succ k ih =>
      intro δmin δmax hk
      simp only [bisectBucketTolerance] at hk
      split at hk
      · rename_i htest
        cases hk
        exact hle _ _ htest
      · exact ih _ _ hk
  -- the growth phase only chooses where the bisection starts
  simp only [bucketTolerance] at h
  split at h
  · exact absurd h (by simp)
  · exact key _ _ _ h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
