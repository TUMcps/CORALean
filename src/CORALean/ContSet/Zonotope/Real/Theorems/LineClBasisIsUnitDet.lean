module

public import CORALean.ContSet.Zonotope.Real.Operations.LineClBasis
public import CORALean.ContSet.Zonotope.Real.Theorems.LineClKeepIsUnitDet

@[expose] public section

/-!
# The clustering basis is invertible

`reduceByBasis_outer` asks of its matrix that the determinant be a unit, and
[1, Alg. 3] does not say how `L⁻¹` exists. `lineClBasis` discharges it: `lineClKeep`
never keeps a singular candidate, so the best of the runs is invertible, and
where no run is the answer is `1`.

## Inputs
* `Z` – zonotope
* `part` – split of the generators
* `ξ` – convergence threshold
* `fuel` – iteration budget
* `runs` – number of restarts

## Hypotheses
* none

## Conclusion
* the returned basis is invertible

## References

* [1] [A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of Zonotopes". 2017
      IEEE 56th Annual Conference on Decision and Control (CDC),
      2017.](../../../../../../references/2017/kopetzki-cdc-order-reduction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The basis line clustering returns is invertible. -/
theorem Zonotope.lineClBasis_isUnit_det (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) (ξ : ℝ) (fuel runs : ℕ) : -- --- CONCL ---
    IsUnit (Z.lineClBasis part ξ fuel runs).det := by -- --- PROOF ---
  unfold Zonotope.lineClBasis
  have key : ∀ (f : ℕ → Mat ℝ n n) (l : List ℕ) (acc : Option (Mat ℝ n n)),
      (∀ M, acc = some M → IsUnit M.det) →
      ∀ M, l.foldl (fun best t => Zonotope.lineClKeep (Z.lineClVolume part) best (f t)) acc
        = some M → IsUnit M.det := by
    intro f l
    induction l with
    | nil => intro acc h; exact h
    | cons t l ih =>
      intro acc h
      exact ih _ (Zonotope.lineClKeep_isUnit_det _ h _)
  generalize hL : (List.range runs).foldl _ none = Lmin
  cases Lmin with
  | none => simp
  | some M => exact key _ _ none (by simp) M hL


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
