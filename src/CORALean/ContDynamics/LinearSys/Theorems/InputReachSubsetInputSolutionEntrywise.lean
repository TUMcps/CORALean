module

public import CORALean.ContDynamics.LinearSys.Definitions.InputRemainderEntrywiseSet
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsExpRemainderEntryLe
public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionEntrywise
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableReflectIoc
public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionOuterOfRemainder
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# `inputSolutionEntrywise` contains everything the input can contribute over a step

`inputReach_subset_inputSolution` for CORA's entrywise remainder [1]. The orders up to `η` are exact
and `r · (e^{τA} - Σ_{i≤η}(τA)ⁱ/i!)` is entrywise under `E(r,η)·r` for every `τ ≤ r`
(`abs_expRemainder_entry_le`), so the generic enclosure applies with no condition on `η`.

## Inputs
* `sys` – linear system
* `r` – step length
* `η` – Taylor order
* `U` – input set

## Hypotheses
* `hr` – step length positive
* `hconv` – input set convex
* `hclosed` – input set closed
* `hbdd` – input set bounded
* `hRconv` – remainder image of the input set convex
* `hRclosed` – remainder image of the input set closed
* `hRbdd` – remainder image of the input set bounded

## Conclusion
* every input's contribution lies in the input solution

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet ContSetLike Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] in
theorem LinearSys.inputReach_subset_inputSolutionEntrywise [Mtimes ℐ S]
    (sys : LinearSys 𝕋 n) {r : ℝ} (hr : 0 < r) (η : ℕ) {U : S n}
    (hconv : Convex ℝ (toSet U)) (hclosed : IsClosed (toSet U))
    (hbdd : Bornology.IsBounded (toSet U))
    (hRconv : Convex ℝ (sys.inputRemainderEntrywiseSet r η U))
    (hRclosed : IsClosed (sys.inputRemainderEntrywiseSet r η U))
    (hRbdd : Bornology.IsBounded (sys.inputRemainderEntrywiseSet r η U)) : -- --- CONCL ---
    sys.inputReach U r ⊆ toSet (sys.inputSolutionEntrywise r η U) := by -- --- PROOF ---
  rintro _ ⟨u, hmem, hmeas, rfl⟩
  refine sys.inputSolution_outer_of_remainder hr η
    (MatExp.inputRemainderEntrywise (toRealMat sys.A) r η) ?_ hconv hclosed hbdd hRconv hRclosed
    hRbdd ?_ (aestronglyMeasurable_reflect_Ioc hmeas)
  · -- every scaled remainder is entrywise under `E(r,η) · r`
    intro τ hτ
    refine Interval.mem_mat_iff.mpr fun j k => ?_
    have hb := MatExp.abs_expRemainder_entry_le (toRealMat sys.A) hτ.1.le hτ.2 η j k
    rw [abs_le] at hb
    refine ⟨?_, ?_⟩
    · show -(r * _) ≤ r * _
      nlinarith [hb.1, hr.le]
    · show r * _ ≤ r * _
      nlinarith [hb.2, hr.le]
  · intro σ hσ
    exact hmem _ ⟨by linarith [hσ.2], by linarith [hσ.1]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
