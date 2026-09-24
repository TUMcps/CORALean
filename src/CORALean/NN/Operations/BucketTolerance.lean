import CORALean.NN.Operations.BisectBucketTolerance
import CORALean.NN.Operations.GrowBucketTolerance
import CORALean.NN.Operations.MaxOver
import CORALean.NN.Operations.MinOver

/-!
# [1, Alg. 1]: the bucket tolerance a reduction rate asks for

[1, Alg. 1] turns a reduction rate `ρ` into merge buckets: grow `δmax` tenfold until at most
`ρ n_k` neurons would remain, then bisect `[δmin, δmax]` until the fraction remaining is `≈ ρ`,
and return the buckets at that `δ`, one mask, `true` on a merged neuron.

Written once over the scalar, every decision through the caller's `le` — `FloatOps.le` at a
machine scalar, where it runs. Neither loop is bounded in [1], and the first need not end, so
both take `fuel` and the result is an `Option`. Nothing here is a soundness hypothesis — [1]'s
Prop. 4 holds at every bucket — so which way anything rounds decides which buckets come out,
never whether the reduction is sound; `bucketTolerance_approx` is line 16's exit condition.

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

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the merge buckets `B_{k,δ}` of the layer bounded by `I_k = [l_k, u_k]` that
leave `≈ ρ n_k` of its neurons, `none` where `fuel` runs out first. -/
def bucketTolerance (le : 𝕋 → 𝕋 → Bool) (tol : 𝕋) (fuel : ℕ) (B : MergeBuckets 𝕋)
    (I_k : Interval (Vec 𝕋 n)) (ρ : 𝕋) : Option (Fin n → Bool) :=
  let δmin := (zero : 𝕋)                                            -- Alg. 1, line 1
  let δmax := subUp (maxOver I_k.sup) (minOver I_k.inf)             -- Alg. 1, line 1
  match growBucketTolerance le B I_k ρ δmax fuel with               -- Alg. 1, lines 2-6
  | none => none
  | some δmax => bisectBucketTolerance le tol B I_k ρ δmin δmax fuel  -- Alg. 1, lines 7-17

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
