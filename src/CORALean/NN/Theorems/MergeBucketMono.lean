module

public import CORALean.NN.Definitions.IsInMergeBucket

@[expose] public section

/-!
# The bucket grows with the tolerance

The fact everything else about [1]'s Alg. 1 rate search rests on: widening `δ`
only ever adds neurons to `IsInMergeBucket Y y δ`, never removes one, since both
halves of `IsInMergeBucket`'s conjunction are one-sided bounds on `δ`.
`mergeBucket_card_mono` turns this into the search's monotone quantity and
`exists_mergeBucket_all` into its endpoint.

## Inputs
* `n` – layer width
* `Y` – bounds of the layer's neurons
* `y` – merge value
* `δ` – smaller tolerance
* `δ'` – larger tolerance
* `i` – neuron index

## Hypotheses
* `hδ` – tolerances are ordered
* `hi` – neuron lies in the bucket at the smaller tolerance

## Conclusion
* the neuron lies in the bucket at the larger tolerance

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research, 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A neuron in a bucket at `δ` stays in the bucket at any wider `δ'`. -/
theorem mergeBucket_mono {n : ℕ} (Y : Real.Interval (Vec ℝ n)) (y : ℝ) {δ δ' : ℝ} (hδ : δ ≤ δ')
    {i : Fin n} (hi : IsInMergeBucket Y y δ i) : IsInMergeBucket Y y δ' i :=
  ⟨by linarith [hi.1], by linarith [hi.2]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
