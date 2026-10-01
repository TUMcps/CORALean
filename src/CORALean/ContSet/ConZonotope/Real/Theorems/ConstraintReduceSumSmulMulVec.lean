import CORALean.ContSet.ConZonotope.Real.Operations.ConstraintReduce

/-!
# `Λ_G` applied to the columns of `A`

The generator correction of [1, Prop. 5]: `Σ_j β_j Λ_G a_j = Λ_G (Aβ)`, with `a_j` the `j`-th
column of `A`. It is what lets `Λ_G (b − Aξ)` be added to `z = Gξ + c` in `constraintReduce_outer`.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Λ_G` applied to the columns of `A`, weighted by `β`, is `Λ_G A β`. -/
theorem ConZonotope.sum_smul_mulVec_columns {n q h : ℕ} (ΛG : Mat ℝ n q) (A : Mat ℝ q h)
    (β : Vec ℝ h) (i : Fin n) :
    (∑ j, β j • (ΛG *ᵥ fun k => A k j)) i = (ΛG *ᵥ (A *ᵥ β)) i := by -- --- PROOF ---
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  simp only [Finset.mul_sum]
  -- swap the two sums, then the terms agree up to commutativity
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
