module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# A box as a zonotope

This is the arrow from intervals to zonotopes of [1, Fig. 1 (Intervals → Zonotopes)].

## Inputs
* `I` – interval

## Hypotheses
* `hI` – lower end below upper end per coordinate

## Conclusion
* zonotope equals the interval

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A nonempty box is exactly its zonotope. -/
theorem Interval.zonotope_exact (I : Interval (Vec ℝ n)) (hI : ∀ i, I.inf i ≤ I.sup i) :
    I.zonotope.construct = I.construct := by -- --- PROOF ---
  refine Set.Subset.antisymm ?_ (Interval.zonotope_contains I)
  rintro x ⟨β, hβ, rfl⟩ i
  -- only the diagonal generator reaches coordinate `i`, at a coefficient in `[-1, 1]`
  have hsum : (∑ j : Fin n, β j •
        (fun i => if i = j then (I.sup i - I.inf i) / 2 else 0 : Vec ℝ n)) i
      = β i * ((I.sup i - I.inf i) / 2) := by
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp only [Pi.smul_apply, smul_eq_mul, if_neg (Ne.symm hj), mul_zero]
    · intro hc
      exact absurd (Finset.mem_univ i) hc
  change I.inf i ≤ (I.inf i + I.sup i) / 2 + (∑ j : Fin n, β j •
      (fun i => if i = j then (I.sup i - I.inf i) / 2 else 0 : Vec ℝ n)) i
    ∧ (I.inf i + I.sup i) / 2 + (∑ j : Fin n, β j •
      (fun i => if i = j then (I.sup i - I.inf i) / 2 else 0 : Vec ℝ n)) i ≤ I.sup i
  rw [hsum]
  have hw : 0 ≤ (I.sup i - I.inf i) / 2 := by linarith [hI i]
  have hb := abs_le.mp (hβ i)
  constructor <;> nlinarith [hb.1, hb.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
