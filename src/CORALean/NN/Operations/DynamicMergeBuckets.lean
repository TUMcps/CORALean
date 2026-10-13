module

public import CORALean.NN.Operations.Bucketed
public import CORALean.NN.Operations.InMergeBucket

@[expose] public section

/-!
# [1, Eq. 6]: merge buckets at the neurons' own centres

One candidate bucket at each neuron's centre `c = (l_k + u_k)/2` in turn, skipping the
neurons already merged so the buckets stay disjoint, and used only when it holds two or more:
a singleton bucket saves nothing. The centre is halved exactly, a binary format only moving
the exponent; its sum rounds up, which only moves the bucket.

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

/-- [1, Eq. 6]'s dynamic buckets, one at each neuron's centre in turn, kept disjoint by
skipping the neurons already merged and used only when they hold two or more. -/
def dynamicMergeBuckets (le : 𝕋 → 𝕋 → Bool) (I : Interval (Vec 𝕋 n)) (δ : 𝕋) : Fin n → Bool :=
  Fin.foldl n (fun merged j =>
      let c := half (addUp (I.inf j) (I.sup j))                     -- [1, Eq. 6]'s `c(j)`
      let B_cδ := fun i => !merged i && inMergeBucket le I c δ i    -- `B_{k,c(j),δ}`, disjoint
      if 2 ≤ bucketed B_cδ then fun i => merged i || B_cδ i else merged)  -- used if not a singleton
    fun _ => false

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
