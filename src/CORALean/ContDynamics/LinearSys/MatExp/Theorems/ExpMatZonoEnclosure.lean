module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoEnclosure
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoRemainder
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoTaylor
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# The exponential of every matrix a matrix zonotope denotes lies in its enclosure

CORA's `expmInd`, guaranteed [1, Eq. 3]: `e^{A r} ∈ Σ_{i=0}^η (A r)ⁱ/i! ⊕ E(r)` over a matrix
zonotope of `A r`. The truncation lands in the zonotope's own truncation, and what it left out is
a matrix of entries no bigger than the tail bound, a point of the remainder box. **`hε` is
stated at `M.interval.absMax`**, and has to be: it must be checkable from the matrix zonotope
alone, before any particular `A` is fixed, and `norm_le_absMax` carries it to the pointwise
condition `norm_exp_sub_expTaylor_le` needs. The order `η` is unconstrained beyond that: a
bigger one is a tighter enclosure, never a different guarantee.

## Inputs
* `M` – matrix zonotope
* `η` – Taylor order
* `A` – member matrix

## Hypotheses
* `hA` – member lies in the matrix zonotope
* `hε` – dominating norm small enough for the Taylor order

## Conclusion
* the exponential of the member lies in the matrix-zonotope enclosure

## References

* [1] [M. Althoff and J. M. Dolan. "Reachability Computation of Low-Order Models for the Safety
      Verification of High-Order Road Vehicle Models". 2012 American Control Conference (ACC),
      2012.](../../../../../../references/2012/althoff-acc-low-order-models.md)
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.exp_mem_expMatZonoEnclosure (M : Zonotope (Mat ℝ n n)) (η : ℕ)
    {A : Mat ℝ n n} (hA : A ∈ M.construct)
    (hε : ‖M.interval.absMax‖ / ((η : ℝ) + 2) < 1) : -- --- CONCL ---
    exp A ∈ (MatExp.expMatZonoEnclosure M η).construct := by -- --- PROOF ---
  have hnorm : ‖A‖ ≤ ‖M.interval.absMax‖ :=
    Interval.norm_le_absMax (Zonotope.interval_contains M hA)
  have hfrac : ‖A‖ / ((η : ℝ) + 2) ≤ ‖M.interval.absMax‖ / ((η : ℝ) + 2) := by gcongr
  -- the tail at `A`, widened to the one bound the whole zonotope answers for
  have htail : ‖exp A - MatExp.expTaylor A η‖
      ≤ MatExp.expRemainderBound M.interval.absMax η :=
    le_trans (norm_exp_sub_expTaylor_le A η (lt_of_le_of_lt hfrac hε))
      (MatExp.expRemainderBound_mono η hnorm hε)
  have hrem : exp A - MatExp.expTaylor A η ∈ (MatExp.expMatZonoRemainder n
      (MatExp.expRemainderBound M.interval.absMax η)).construct :=
    MatExp.mem_expMatZonoRemainder fun i j => le_trans (abs_entry_le_norm _ i j) htail
  have hmem := Set.add_mem_add (MatExp.expTaylor_mem_expMatZonoTaylor M hA η) hrem
  rw [Zonotope.plus_exact] at hmem
  have heq : MatExp.expTaylor A η + (exp A - MatExp.expTaylor A η) = exp A := by abel
  rw [heq] at hmem
  exact hmem

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
