module

public import CORALean.NN.Operations.InitMergeBuckets
public import CORALean.NN.Operations.Ratio

@[expose] public section

/-!
# [1, Alg. 1, lines 2-6]: growing `δmax` until enough neurons merge

`δmax` is multiplied tenfold until the buckets at it leave at most `ρ n_k` neurons. [1] bounds
the loop by nothing, and it need not end — `δmax` may start at `0` — so it takes `fuel` and
returns `none` past it. The tenfold growth rounds up, a larger `δmax` only widening the
bisection that follows.

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

/-- Lines 2-6: `δmax` grown tenfold until at most `ρ n_k` neurons remain; `none` past `fuel`. -/
def growBucketTolerance (le : 𝕋 → 𝕋 → Bool) (B : MergeBuckets 𝕋) (I_k : Interval (Vec 𝕋 n))
    (ρ : 𝕋) : 𝕋 → ℕ → Option 𝕋
  | _, 0 => none
  | δmax, fuel + 1 =>
    let δmax := nsmulUp 10 δmax                                     -- Alg. 1, line 3
    let B_kδmax := initMergeBuckets le B I_k δmax                   -- Alg. 1, line 4
    let nhat_k := n - bucketed B_kδmax                              -- Alg. 1, line 5
    if le (ratio nhat_k n) ρ then some δmax                         -- Alg. 1, line 6
    else growBucketTolerance le B I_k ρ δmax fuel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
