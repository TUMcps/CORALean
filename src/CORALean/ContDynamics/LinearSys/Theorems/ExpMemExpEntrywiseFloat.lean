module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsExpRemainderEntryLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylorFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpEntrywiseFloat
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter

@[expose] public section

/-!
# `e^{AΔt}` lies in `expEntrywiseFloat`

The exponential is its series up to order `η` and the remainder, which is entrywise under the exact
`E(Δt,η)` of [1] (`abs_expRemainder_entry_le`), which a float bound `W` holds: the series lies in
`expIntervalTaylor` of the box `[AΔt]` and `[-W, W]` widens it by the remainder.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order
* `W` – float bound on the entrywise remainder

## Hypotheses
* `hΔt` – step length nonnegative
* `hW` – the bound holds the exact remainder

## Conclusion
* the exponential of the scaled matrix lies in the float enclosure

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

open CORALean.Float SoundFloatArithmetic NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.exp_mem_expEntrywiseFloat (sys : LinearSys 𝕋 n) {Δt : 𝕋} (η : ℕ)
    (W : Mat 𝕋 n n) (hΔt : 0 ≤ toReal Δt)
    (hW : ∀ j k, Real.MatExp.expRemainderMat (Scalar.toRealMat sys.A) (toReal Δt) η j k
      ≤ toReal (W j k)) : -- --- CONCL ---
    exp (toReal Δt • Scalar.toRealMat sys.A)
      ∈ (sys.expEntrywiseFloat Δt η W).toSet := by -- --- PROOF ---
  have hM : toReal Δt • Scalar.toRealMat sys.A
      ∈ (Interval.smul Δt Δt (Interval.point sys.A)).toSet :=
    Interval.smul_outer le_rfl le_rfl _ (Interval.mem_point sys.A)
  have htay := Real.Interval.mem_mat_iff.mp
    (MatExp.expTaylor_mem_expIntervalTaylor _ hM η)
  rw [LinearSys.expEntrywiseFloat, Interval.materialiseMat_eq]
  refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
  have hb := Real.MatExp.abs_expRemainder_entry_le (Scalar.toRealMat sys.A) hΔt le_rfl η j k
  rw [abs_le] at hb
  have hWjk := hW j k
  obtain ⟨t1, t2⟩ := htay j k
  simp only [Interval.nominal, RealImage.realImage, toRealMat, Matrix.sub_apply] at hb t1 t2 ⊢
  have hsd := subDown_le_sub ((MatExp.expIntervalTaylor
    (Interval.smul Δt Δt (Interval.point sys.A)) η).inf j k) (W j k)
  have hau := add_le_addUp ((MatExp.expIntervalTaylor
    (Interval.smul Δt Δt (Interval.point sys.A)) η).sup j k) (W j k)
  constructor <;> linarith [hb.1, hb.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
