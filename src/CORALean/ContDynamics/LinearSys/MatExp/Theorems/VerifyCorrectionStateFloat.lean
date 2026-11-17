module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyCorrectionStateFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffBound
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffLowTightFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrixEntrywise
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowUpFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ScaledRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.VerifyPowerFloat
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.VerifyCorrSumsFloat

@[expose] public section

/-!
# `MatExp.verifyCorrectionStateFloat` encloses the correction of the exponential

Whatever order `η` the search stops at, `F` is the entrywise correction matrix of order `η - 1`
rounded outward: each term `[κᵢ rⁱ, 0] Aⁱ/i!` holds `corrTerm` (`corrCoeffLowTight` below the
coefficient, `powUp` above `rⁱ`, `verifyPowerFloat` around `Aⁱ/i!`), the sums accumulated down
and up hold the sums of their minima and maxima, and the scaled remainder holds `E(r, η - 1)`.
`expDiff_mem_correctionMatrixEntrywise` then puts `e^{tA} − I − (t/r)(e^{rA} − I)` inside for
every `t ∈ [0, r]`. The stopping rule itself is not used: any stop is sound.

## Inputs
* `A` – float system matrix
* `s` – float scales
* `r` – float step length

## Hypotheses
* `hs` – the scales are positive
* `hr` – the step length is positive

## Conclusion
* for every returned `(η, F)` and every `t ∈ [0, r]`, the correction at `t` lies in `F`
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every entry of the order-`i` correction term lies in the float term. -/
private theorem MatExp.aux_corrTerm_mem (A : Mat 𝕋 n n) {r : 𝕋} (hr : 0 ≤ toReal r) {i : ℕ}
    (hi : 2 ≤ i) (j k : Fin n) : -- --- CONCL ---
    toReal ((MatExp.step_verifyCorrTermFloat A r i).inf j k)
        ≤ Real.MatExp.corrTerm (toRealMat A) (toReal r) i j k
      ∧ Real.MatExp.corrTerm (toRealMat A) (toReal r) i j k
        ≤ toReal ((MatExp.step_verifyCorrTermFloat A r i).sup j k) := by -- --- PROOF ---
  -- the coefficient: below `corrCoeff`, which is `≤ 0`, and `rⁱ` above
  have hκ := MatExp.corrCoeffLowTight_le (𝕋 := 𝕋) hi
  have hc0 : Real.MatExp.corrCoeff i ≤ 0 := by
    have h := Real.MatExp.corrCoeff_le_sub hi (le_refl (0:ℝ))
    rwa [zero_pow (by omega : i ≠ 0), sub_zero] at h
  have hp := MatExp.le_powUp hr i
  have hp0 : 0 ≤ toReal r ^ i := pow_nonneg hr i
  -- the scalar between `cLo` and `0`
  have hlo : toReal (mulDown (MatExp.corrCoeffLowTight (𝕋 := 𝕋) i) (MatExp.powUp i r))
      ≤ Real.MatExp.corrCoeff i * toReal r ^ i :=
    le_trans (mulDown_le_mul _ _) (le_trans
      (mul_le_mul_of_nonneg_right hκ (le_trans hp0 hp))
      (mul_le_mul_of_nonpos_left hp hc0))
  have hhi : Real.MatExp.corrCoeff i * toReal r ^ i ≤ toReal (zero : 𝕋) := by
    rw [toReal_zero]; exact mul_nonpos_of_nonpos_of_nonneg hc0 hp0
  have hmem := Interval.mem_mat_iff.mp (Interval.smul_outer hlo hhi _
    (MatExp.pow_div_factorial_mem_verifyPowerFloat A i)) j k
  simp only [Matrix.smul_apply, smul_eq_mul] at hmem
  have heq : Real.MatExp.corrTerm (toRealMat A) (toReal r) i j k
      = Real.MatExp.corrCoeff i * toReal r ^ i
        * ((Nat.factorial i : ℝ)⁻¹ * (toRealMat A ^ i) j k) := by
    rw [Real.MatExp.corrTerm]
  rw [heq]
  exact hmem


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expDiff_mem_verifyCorrectionStateFloat (A : Mat 𝕋 n n) {s : Vec 𝕋 n}
    (hs : ∀ i, 0 < toReal (s i)) {r : 𝕋} (hr : 0 < toReal r) : -- --- CONCL ---
    ∀ p ∈ MatExp.verifyCorrectionStateFloat A s r, ∀ t : ℝ, 0 ≤ t → t ≤ toReal r →
      exp (t • toRealMat A) - 1 - (t / toReal r) • (exp (toReal r • toRealMat A) - 1)
        ∈ p.2.toSet := by -- --- PROOF ---
  rintro ⟨η, F⟩ hF t ht0 htr
  rw [Option.mem_def] at hF
  unfold MatExp.verifyCorrectionStateFloat at hF
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at hF
  obtain ⟨η', hfind, W, hW, rfl, rfl⟩ := hF
  -- the order is at least `3`: the remainder's order `η - 1` is `m + 2`
  have hη3 : 3 ≤ η' := by
    have hmem := List.mem_of_find?_eq_some hfind
    rw [List.mem_range'_1] at hmem
    omega
  obtain ⟨m, rfl⟩ : ∃ m, η' = m + 3 := ⟨η' - 3, by omega⟩
  -- the real entrywise matrix holds the correction
  have hX := Real.Interval.mem_mat_iff.mp
    (Real.MatExp.expDiff_mem_correctionMatrixEntrywise (toRealMat A) hr (m := m) ht0 htr)
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  obtain ⟨h1, h2⟩ := hX j k
  simp only [Real.MatExp.correctionMatrixEntrywise, show m + 2 - 1 = m + 1 from rfl] at h1 h2
  -- the remainder, the terms and their sums, each in its float bound
  have hWjk := MatExp.expRemainderMat_le_scaledRemainderFloat A hs hr.le (m + 2)
    W (Option.mem_def.mpr hW) j k
  have hterm := fun i : ℕ => MatExp.aux_corrTerm_mem A hr.le (i := i + 2) (by omega) j k
  set T := fun i => MatExp.step_verifyCorrTermFloat A r (i + 2) with hT
  obtain ⟨hlo, hhi⟩ := MatExp.verifyCorrSumsFloat_bracket T
    (fun i => Real.MatExp.corrTerm (toRealMat A) (toReal r) (i + 2) j k) j k (fun i => hterm i)
    (m + 1)
  simp only [Interval.materialiseMat_eq, show m + 3 - 2 = m + 1 from rfl]
  -- the outward rounding of the last addition
  have hsd := subDown_le_sub ((MatExp.verifyCorrSumsFloat ((List.range (m + 1)).map T)).inf j k)
    (W j k)
  have hau := add_le_addUp ((MatExp.verifyCorrSumsFloat ((List.range (m + 1)).map T)).sup j k)
    (W j k)
  exact ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
