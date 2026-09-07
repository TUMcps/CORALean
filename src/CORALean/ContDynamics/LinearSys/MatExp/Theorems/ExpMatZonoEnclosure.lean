import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoRemainder
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoTaylor
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

/-!
# The exponential of every matrix a matrix zonotope denotes lies in its enclosure

CORA's `expmInd`, guaranteed: the truncation lands in the zonotope's own
truncation, and what it left out is a matrix of entries no bigger than the tail
bound, which is a point of the remainder box.

**`hε` is stated at `M.interval.absMax`**, and has to be: it must be checkable
from the matrix zonotope alone, before any particular `A` is fixed, and
`norm_le_absMax` is what carries it to the pointwise condition
`norm_exp_sub_expTaylor_le` needs.

The order `η` is unconstrained beyond that — a bigger one is a tighter
enclosure, never a different guarantee.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.exp_mem_expMatZonoEnclosure (M : Zonotope (Mat ℝ n n)) (η : ℕ)
    {A : Mat ℝ n n} (hA : A ∈ M.construct)
    (hε : ‖M.interval.absMax‖ / ((η : ℝ) + 2) < 1) :
    exp A ∈ (MatExp.expMatZonoEnclosure M η).construct := by -- --- PROOF ---
  have hnorm : ‖A‖ ≤ ‖M.interval.absMax‖ :=
    Interval.norm_le_absMax (Zonotope.interval_outer M hA)
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
