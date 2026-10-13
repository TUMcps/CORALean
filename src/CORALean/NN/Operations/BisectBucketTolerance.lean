import CORALean.NN.Operations.InitMergeBuckets
import CORALean.NN.Operations.Ratio

/-!
# [1, Alg. 1, lines 7-17]: bisecting the bucket tolerance

`[δmin, δmax]` is halved until the fraction of neurons the buckets at its midpoint leave is
within `tol` of `ρ`, and those buckets are returned. [1] leaves `≈` open; it is
`|n̂_k/n_k - ρ| ≤ tol` here, the difference rounded up before its absolute value is taken.
Like the growth phase, the loop takes `fuel` and returns `none` past it.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 7-16: bisect `[δmin, δmax]` until `n̂_k/n_k ≈ ρ`; `none` past `fuel`. -/
def bisectBucketTolerance (le : 𝕋 → 𝕋 → Bool) (tol : 𝕋) (B : MergeBuckets 𝕋)
    (I_k : Interval (Vec 𝕋 n)) (ρ : 𝕋) : 𝕋 → 𝕋 → ℕ → Option (Fin n → Bool)
  | _, _, 0 => none
  | δmin, δmax, fuel + 1 =>
    let δ := half (addUp δmin δmax)                                 -- Alg. 1, line 8
    let B_kδ := initMergeBuckets le B I_k δ                         -- Alg. 1, line 9
    let nhat_k := n - bucketed B_kδ                                 -- Alg. 1, line 10
    let tooManyMerged := !le (mulUp ρ (nsmulUp n one)) (nsmulDown nhat_k one)  -- Alg. 1, line 11
    let δmax := if tooManyMerged then δ else δmax                   -- Alg. 1, line 12
    let δmin := if tooManyMerged then δmin else δ                   -- Alg. 1, line 14
    if le (absolute (subUp (ratio nhat_k n) ρ)) tol then some B_kδ  -- Alg. 1, lines 16-17
    else bisectBucketTolerance le tol B I_k ρ δmin δmax fuel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
