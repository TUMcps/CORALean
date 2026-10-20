module

public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Raising labels does not lower the vertex sum

On the box `[0, b₁] × … × [0, bₙ]`, `b ≥ 0`, a vertex raising every coordinate another raises has
at least its sum. [1, Lemma 6.5] rests on it: a piece of the partition, its later coordinates
all raised, lies above the vertex line 6 rejected.

## Inputs
* `b` – upper bound vector
* `l` – lower corner labels
* `w` – raised corner labels

## Hypotheses
* `hb0` – bounds nonnegative
* `hlw` – every label of `l` is also in `w`

## Conclusion
* the corner sum does not decrease

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.corner_sum_mono {b : Vec ℝ n} (hb0 : ∀ i, 0 ≤ b i) {l w : Fin n → Bool}
    (hlw : ∀ i, l i = true → w i = true) : -- --- CONCL ---
    ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner l i ≤
      ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner w i := by -- --- PROOF ---
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Interval.corner]
  cases hli : l i
  · cases hwi : w i <;> simp [hb0 i]
  · simp [hlw i hli]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
