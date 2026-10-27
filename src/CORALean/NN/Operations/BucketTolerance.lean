module

public import CORALean.NN.Operations.GrowBucketTolerance
public import CORALean.NN.Operations.InitMergeBuckets
public import CORALean.NN.Operations.MaxOver
public import CORALean.NN.Operations.MinOver
public import CORALean.NN.Operations.Ratio

@[expose] public section

/-!
# [1, Alg. 1]: the bucket tolerance a reduction rate asks for

[1, Alg. 1] turns a reduction rate `ρ` into merge buckets: grow `δmax` tenfold until at most `ρ n_k`
neurons would remain, then bisect `[δmin, δmax]` until the fraction remaining is `≈ ρ`, and return
the buckets at that `δ`, one mask, `true` on a merged neuron. Written once over the scalar, every
decision through the caller's `le` (`FloatOps.le` at a machine scalar). Neither loop is bounded in
[1], so both take `fuel` and the result is an `Option`. Nothing here is a soundness hypothesis —
[1]'s Prop. 4 holds at every bucket — so rounding decides which buckets come out, never whether the
reduction is sound; `bucketTolerance_approx` is line 16's exit condition.

## Inputs
* `le` – comparison of two scalars
* `tol` – tolerance on the remaining fraction
* `fuel` – bound on the loop iterations
* `B` – merge bucket initialisation
* `I_k` – bounds of the layer
* `ρ` – reduction rate

## Output
* mask of the merged neurons, or none if the fuel runs out

## References

* [1] [T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../references/2023/ladner-tmlr-network-reduction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Lines 7-16: bisect `[δmin, δmax]` until `n̂_k/n_k ≈ ρ`; `none` past `fuel`. -/
def aux_bisectBucketTolerance (le : 𝕋 → 𝕋 → Bool) (tol : 𝕋) (B : MergeBuckets 𝕋)
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
    else aux_bisectBucketTolerance le tol B I_k ρ δmin δmax fuel


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the merge buckets `B_{k,δ}` of the layer bounded by `I_k = [l_k, u_k]` that
leave `≈ ρ n_k` of its neurons, `none` where `fuel` runs out first. -/
def bucketTolerance (le : 𝕋 → 𝕋 → Bool) (tol : 𝕋) (fuel : ℕ) (B : MergeBuckets 𝕋)
    (I_k : Interval (Vec 𝕋 n)) (ρ : 𝕋) : Option (Fin n → Bool) :=
  -- 1. `δmin ← 0`
  let δmin := (zero : 𝕋)
  -- 1. `δmax ← max(u_k) − min(l_k)`
  let δmax := subUp (maxOver I_k.sup) (minOver I_k.inf)
  -- 2. `do` 3. `δmax ← 10 δmax` … 6. `while n̂_k / n_k > ρ`: 1) the upper bound for the tolerance
  match growBucketTolerance le B I_k ρ δmax fuel with
  | none => none
  | some δmax =>
    -- 7. `do` 8. `δ ← (δmin + δmax) / 2` … 16. `while n̂_k / n_k ≉ ρ`, 17. `return B_{k,δ}`
    aux_bisectBucketTolerance le tol B I_k ρ δmin δmax fuel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
