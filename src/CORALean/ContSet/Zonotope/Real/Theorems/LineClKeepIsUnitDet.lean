module

public import CORALean.ContSet.Zonotope.Real.Operations.LineClKeep

@[expose] public section

/-!
# `lineClKeep` only ever keeps an invertible matrix

What [1, Alg. 3, lines 14-17] holds on to has an invertible matrix, whatever the
volumes say: a candidate is kept only if its determinant is a unit, and otherwise
the old best stays, which was one by induction.

## Inputs
* `V` – volume function
* `best` – best basis so far
* `L` – candidate basis

## Hypotheses
* `hbest` – the best basis is invertible

## Conclusion
* the kept basis is invertible

## References

* [1] A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of
      Zonotopes". In Proc. of the 56th IEEE Conference on Decision and Control (CDC), pp.
      5626-5633, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A step of the selection keeps invertible matrices only. -/
theorem Zonotope.lineClKeep_isUnit_det (V : Mat ℝ n n → ℝ) {best : Option (Mat ℝ n n)}
    (hbest : ∀ M, best = some M → IsUnit M.det) (L : Mat ℝ n n) : -- --- CONCL ---
    ∀ M, Zonotope.lineClKeep V best L = some M → IsUnit M.det := by -- --- PROOF ---
  intro M hM
  unfold Zonotope.lineClKeep at hM
  split_ifs at hM with h
  · obtain rfl := Option.some.inj hM
    exact h.1
  · exact hbest M hM


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
