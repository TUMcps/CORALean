module

public import CORALean.NN.Definitions.MergeBucket

@[expose] public section

/-!
# A bucketed neuron's width

ℝ-only, the bucket being read off exact bounds: both `y ± δ` lie between a bucketed neuron's
bounds, so they are within `2δ` of each other.

## Inputs
* `n` – layer width
* `Y` – bounds of the layer's neurons
* `y` – merge value
* `δ` – merge tolerance
* `i` – neuron index

## Hypotheses
* `hi` – neuron lies in the bucket

## Conclusion
* the neuron's bounds are at most twice the tolerance apart
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A bucketed neuron's bounds are within `2δ` of each other, `y ± δ` both between them. -/
theorem mergeBucket_width {n : ℕ} (Y : Real.Interval (Vec ℝ n)) (y δ : ℝ) {i : Fin n}
    (hi : mergeBucket Y y δ i) : Y.sup i - Y.inf i ≤ 2 * δ := by
  linarith [hi.1, hi.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
