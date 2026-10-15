module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureExactFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosureFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylorExactFloat

@[expose] public section

/-!
# The matrix exponential lies in the sharper float interval enclosure

The float counterpart of `Real.MatExp.exp_mem_expIntervalEnclosureExact`, entry by entry as
`exp_mem_expIntervalEnclosure` does and with the same tail bound at `normUpperBound`: only the
center differs. `hε` asks `1/2`, as there, since `expRemainderBound_le`'s geometric factor is
the fixed constant `2`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.exp_mem_expIntervalEnclosureExact (A : Interval (Mat 𝕋 n n)) (t : 𝕋)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) {κ : ℕ} (hκ : 2 ≤ κ)
    (hε : toReal (MatExp.normUpperBound (Interval.smul t t A)) / ((κ : ℝ) + 2) ≤ 1 / 2) :
    exp (toReal t • M) ∈
      (MatExp.expIntervalEnclosureExact A t κ).construct := by -- --- PROOF ---
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have hMB : toReal t • M ∈ (Interval.smul t t A).construct :=
    Interval.smul_outer (le_refl _) (le_refl _) A hM
  have htay := Interval.mem_mat_iff.mp (MatExp.expTaylor_mem_expIntervalTaylorExact A t hM hκ) i j
  have hb := MatExp.abs_entry_exp_sub_expTaylor_le (Interval.smul t t A) κ hMB hε i j
  rw [abs_le] at hb
  constructor
  · show toReal (subDown ((MatExp.expIntervalTaylorExact A t κ).inf i j)
        (MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul t t A)) κ)) ≤ _
    have hsd := subDown_le_sub ((MatExp.expIntervalTaylorExact A t κ).inf i j)
      (MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul t t A)) κ)
    linarith [hsd, htay.1, hb.1]
  · show _ ≤ toReal (addUp ((MatExp.expIntervalTaylorExact A t κ).sup i j)
        (MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul t t A)) κ))
    have hau := add_le_addUp ((MatExp.expIntervalTaylorExact A t κ).sup i j)
      (MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul t t A)) κ)
    linarith [hau, htay.2, hb.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
