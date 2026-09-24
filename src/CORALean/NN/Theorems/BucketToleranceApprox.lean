import CORALean.NN.Operations.BucketTolerance

/-!
# What [1, Alg. 1] returns meets the reduction rate

Line 16 is the only exit of the bisection, so the buckets returned are ones the test there
passed at: the fraction of neurons they leave is within `tol` of `ρ`, as the scalar computed
that difference. That is all [1, Alg. 1] promises. It says nothing of which neurons merge, and
needs not: Prop. 4 is sound at every bucket. `le` need only be sound on a `true`; at `𝕋 := ℝ`
every rounding is exact and this is `|n̂_k/n_k - ρ| ≤ tol` itself.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1]: the buckets returned leave `n̂_k` neurons with `|n̂_k/n_k - ρ| ≤ tol`, the
difference as the scalar computes it. -/
theorem bucketTolerance_approx {le : 𝕋 → 𝕋 → Bool}
    (hle : ∀ a b, le a b = true → toReal a ≤ toReal b)
    {tol : 𝕋} {fuel : ℕ} {B : MergeBuckets 𝕋} {I_k : Interval 𝕋 n} {ρ : 𝕋}
    {B_kδ : Fin n → Bool} (h : bucketTolerance le tol fuel B I_k ρ = some B_kδ) :
    |toReal (subUp (ratio (n - bucketed B_kδ) n) ρ)| ≤ toReal tol := by -- --- PROOF ---
  -- the bisection returns only where line 16's test passed, at every fuel
  have key : ∀ (k : ℕ) (δmin δmax : 𝕋),
      bisectBucketTolerance le tol B I_k ρ δmin δmax k = some B_kδ →
        |toReal (subUp (ratio (n - bucketed B_kδ) n) ρ)| ≤ toReal tol := by
    intro k
    induction k with
    | zero => intro _ _ h0; exact absurd h0 (by simp [bisectBucketTolerance])
    | succ k ih =>
      intro δmin δmax hk
      simp only [bisectBucketTolerance] at hk
      split at hk
      · rename_i htest
        cases hk
        rw [← toReal_absolute]
        exact hle _ _ htest
      · exact ih _ _ hk
  -- the growth phase only chooses where the bisection starts
  simp only [bucketTolerance] at h
  split at h
  · exact absurd h (by simp)
  · exact key _ _ _ h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
