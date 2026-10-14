module

public import CORALean.NN.Operations.InMergeBucket

@[expose] public section

/-!
# [1, Eq. 5]: merge buckets at an activation's asymptotic values

One bucket per stored value `y` — `[0, 1]` for sigmoid, `[-1, 1]` for tanh, `[0]` for ReLU —
returned as one mask, `true` on a merged neuron: a bucket is only ever used through the
neurons it merges. A neuron two buckets hold belongs to the first.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 5]'s static buckets `B_{k,y,δ}`, one per asymptotic value `y`: a neuron is merged
when one of them holds it, and belongs to the first that does. -/
def staticMergeBuckets (le : 𝕋 → 𝕋 → Bool) (ys : List 𝕋) (I : Interval (Vec 𝕋 n)) (δ : 𝕋) :
    Fin n → Bool :=
  fun i => ys.any fun y => inMergeBucket le I y δ i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
