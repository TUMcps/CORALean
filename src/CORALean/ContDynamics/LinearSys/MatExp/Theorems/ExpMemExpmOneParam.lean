module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpTaylorMemExpmOneParam
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoRemainder
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpMatZonoRemainder
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# The matrix exponential set of one parameter lies in `K(r) ⊕ E(r)`

[1, Thm. 1]: `{e^{Ar} | A = C + βG, β ∈ [-1, 1]} ⊆ K(r) ⊕ E(r)`. The Taylor polynomial is in `K(r)`
(`MatExp.expTaylor_mem_expmOneParam`), and what it leaves out is in `E(r)`, the remainder box
[1, Eq. 3] takes from the earlier work: the tail bound at the dominating matrix of the matrix
zonotope `{rC + βrG}`'s interval hull, as for `MatExp.expMatZonoEnclosure`. `hε` is that bound's
convergence condition,
checkable from `C`, `G`, `r` and `η` alone. "Tightly" is not formalized; the enclosure is.

## References

* [1] M. Althoff and J. M. Dolan. "Reachability Computation of Low-Order Models for the Safety
      Verification of High-Order Road Vehicle Models". In Proc. of the American Control
      Conference, pp. 3559-3566, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: `e^{(C + βG) r} ∈ K(r) ⊕ E(r)` for every `β ∈ [-1, 1]`. -/
theorem MatExp.exp_mem_expmOneParam (C G : Mat ℝ n n) (r : ℝ) (η : ℕ) {β : ℝ} (hβ : |β| ≤ 1)
    (hε : ‖(⟨1, r • C, fun _ => r • G⟩ : Zonotope (Mat ℝ n n)).interval.absMax‖ /
      ((η : ℝ) + 2) < 1) : -- --- STMT ---
    exp (r • (C + β • G)) ∈ ((MatExp.expmOneParam C G r η).plus (MatExp.expMatZonoRemainder n
      (MatExp.expRemainderBound (⟨1, r • C, fun _ => r • G⟩ : Zonotope (Mat ℝ n n)).interval.absMax
        η))).construct := by -- --- PROOF ---
  set M : Zonotope (Mat ℝ n n) := ⟨1, r • C, fun _ => r • G⟩
  -- `r (C + βG)` is a member of the matrix zonotope `{rC + βrG}`
  have hA : r • (C + β • G) ∈ M.construct := ⟨fun _ => β, fun _ => hβ, by
    simp only [M, Finset.univ_unique, Finset.sum_singleton, smul_add, smul_smul, mul_comm]⟩
  have hnorm : ‖r • (C + β • G)‖ ≤ ‖M.interval.absMax‖ :=
    Interval.norm_le_absMax (Zonotope.interval_contains M hA)
  have hfrac : ‖r • (C + β • G)‖ / ((η : ℝ) + 2) ≤ ‖M.interval.absMax‖ / ((η : ℝ) + 2) := by
    gcongr
  -- the tail at this member, widened to the bound the whole set answers for
  have htail : ‖exp (r • (C + β • G)) - MatExp.expTaylor (r • (C + β • G)) η‖
      ≤ MatExp.expRemainderBound M.interval.absMax η :=
    le_trans (norm_exp_sub_expTaylor_le _ η (lt_of_le_of_lt hfrac hε))
      (MatExp.expRemainderBound_mono η hnorm hε)
  have hrem : exp (r • (C + β • G)) - MatExp.expTaylor (r • (C + β • G)) η ∈
      (MatExp.expMatZonoRemainder n (MatExp.expRemainderBound M.interval.absMax η)).construct :=
    MatExp.mem_expMatZonoRemainder fun i j => le_trans (abs_entry_le_norm _ i j) htail
  have hmem := Set.add_mem_add (MatExp.expTaylor_mem_expmOneParam C G r η hβ) hrem
  rw [Zonotope.plus_exact, add_sub_cancel] at hmem
  exact hmem

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
