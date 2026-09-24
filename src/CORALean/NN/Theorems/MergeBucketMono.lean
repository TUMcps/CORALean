import CORALean.NN.Definitions.MergeBucket

/-!
# The bucket grows with the tolerance

The fact everything else about [1]'s Alg. 1 rate search rests on: widening `δ`
only ever adds neurons to `mergeBucket Y y δ`, never removes one, since both
halves of `mergeBucket`'s conjunction are one-sided bounds on `δ`.
`mergeBucket_card_mono` turns this into the search's monotone quantity and
`exists_mergeBucket_all` into its endpoint.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A neuron in a bucket at `δ` stays in the bucket at any wider `δ'`. -/
theorem mergeBucket_mono {n : ℕ} (Y : Real.Interval (Vec ℝ n)) (y : ℝ) {δ δ' : ℝ} (hδ : δ ≤ δ')
    {i : Fin n} (hi : mergeBucket Y y δ i) : mergeBucket Y y δ' i :=
  ⟨by linarith [hi.1], by linarith [hi.2]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
