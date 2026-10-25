module

public import CORALean.NN.Theorems.MergeBucketMono

@[expose] public section

/-!
# So the counts move monotonically

`Fintype.card {i // IsInMergeBucket Y y δ i}` is exactly the index count of
`(mergeSplit Y y δ).right`, by the definition of `Partition.ofPred` — the
bucket's size, and the survivor count's fall, as `δ` widens. That is the
quantity [1]'s Alg. 1 binary search on `δ` is searching, and `mergeBucket_mono`
is why it only ever grows: the inclusion it gives, restricted to the
underlying `Fin n`, is an injection from the smaller bucket into the larger one.

## Inputs
* `n` – layer width
* `Y` – bounds of the layer's neurons
* `y` – merge value
* `δ` – smaller tolerance
* `δ'` – larger tolerance

## Hypotheses
* `hδ` – tolerances are ordered

## Conclusion
* the bucket's neuron count does not shrink with the tolerance

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- Widening the tolerance can only grow the bucket's index count, never shrink it. -/
theorem mergeBucket_card_mono {n : ℕ} (Y : Real.Interval (Vec ℝ n)) (y : ℝ) {δ δ' : ℝ}
    (hδ : δ ≤ δ') : -- --- CONCL ---
    Fintype.card {i : Fin n // IsInMergeBucket Y y δ i}
      ≤ Fintype.card {i : Fin n // IsInMergeBucket Y y δ' i} := by -- --- PROOF ---
  apply Fintype.card_le_of_injective (fun x => ⟨x.val, mergeBucket_mono Y y hδ x.property⟩)
  -- the map is the identity on the underlying `Fin n`, so equal images force equal sources
  intro a b hab
  have h := congrArg Subtype.val hab
  exact Subtype.ext h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
