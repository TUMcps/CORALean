module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyCorrectionInputFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffBound
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffLowTightFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrixEntrywise
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowUpFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ScaledRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.VerifyPowerFloat
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.VerifyCorrSumsFloat

@[expose] public section

/-!
# `MatExp.verifyCorrectionInputFloat` encloses the correction of the input integral

Whatever order `η` the search stops at, `G` is the entrywise input correction matrix with the
`η - 2` terms before the stop, rounded outward: each term `[κ r^{i+2}/(i+2), 0] A^{i+1}/(i+1)!`
holds `constCorrTerm i` (`corrCoeffLowTight` below the coefficient, `powUp` above the power of
`r`, the division by `i + 2` from below on a nonpositive number, `verifyPowerFloat` around the
power), the sums accumulated down and up hold the sums of their minima and maxima, and `r` times
the scaled remainder holds `r E(r, η - 2)`. `expIntegralDiff_mem_constCorrectionMatrixEntrywise`
puts `∫₀ᵗ e^{Aσ}dσ − (t/r)∫₀ʳ e^{Aσ}dσ` inside for every `t ∈ [0, r]`.

## Inputs
* `A` – float system matrix
* `s` – float scales
* `r` – float step length

## Hypotheses
* `hs` – the scales are positive
* `hr` – the step length is positive

## Conclusion
* for every returned `(η, G)` and every `t ∈ [0, r]`, the input correction at `t` lies in `G`
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

/-- Every entry of the `i`-th input correction term lies in the float term. -/
private theorem MatExp.aux_constCorrTerm_mem (A : Mat 𝕋 n n) {r : 𝕋} (hr : 0 ≤ toReal r)
    (i : ℕ) (j k : Fin n) : -- --- CONCL ---
    toReal ((MatExp.step_verifyConstCorrTermFloat A r i).inf j k)
        ≤ Real.MatExp.constCorrTerm (toRealMat A) (toReal r) i j k
      ∧ Real.MatExp.constCorrTerm (toRealMat A) (toReal r) i j k
        ≤ toReal ((MatExp.step_verifyConstCorrTermFloat A r i).sup j k) := by -- --- PROOF ---
  -- the coefficient: below `corrCoeff`, which is `≤ 0`, and `r^η` above
  have hi : 2 ≤ i + 2 := by omega
  have hκ := MatExp.corrCoeffLowTight_le (𝕋 := 𝕋) hi
  have hc0 : Real.MatExp.corrCoeff (i + 2) ≤ 0 := by
    have h := Real.MatExp.corrCoeff_le_sub hi (le_refl (0:ℝ))
    rwa [zero_pow (by omega : i + 2 ≠ 0), sub_zero] at h
  have hp := MatExp.le_powUp hr (i + 2)
  have hp0 : 0 ≤ toReal r ^ (i + 2) := pow_nonneg hr _
  set y := Real.MatExp.corrCoeff (i + 2) * toReal r ^ (i + 2)
  have hy0 : y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0 hp0
  -- the product below `y`
  have hc : toReal (mulDown (MatExp.corrCoeffLowTight (𝕋 := 𝕋) (i + 2))
      (MatExp.powUp (i + 2) r)) ≤ y :=
    le_trans (mulDown_le_mul _ _) (le_trans
      (mul_le_mul_of_nonneg_right hκ (le_trans hp0 hp))
      (mul_le_mul_of_nonpos_left hp hc0))
  -- the divisor between `1` and `i + 2`
  set d : 𝕋 := maximum one (nsmulDown (i + 2) one)
  have hd1 : 1 ≤ toReal d := by rw [toReal_maximum, toReal_one]; exact le_max_left _ _
  have hdk : toReal d ≤ ((i + 2 : ℕ) : ℝ) := by
    have h := nsmulDown_le (i + 2) (one : 𝕋)
    rw [toReal_one, mul_one] at h
    rw [toReal_maximum, toReal_one]
    exact max_le (by exact_mod_cast (show 1 ≤ i + 2 by omega)) h
  -- the quotient by the divisor stays below `y / (i + 2)`
  have hd0 : 0 < toReal d := by linarith
  have hk0 : (0 : ℝ) < ((i + 2 : ℕ) : ℝ) := by positivity
  have hlo : toReal (divDown (mulDown (MatExp.corrCoeffLowTight (𝕋 := 𝕋) (i + 2))
      (MatExp.powUp (i + 2) r)) d) ≤ y / ((i + 2 : ℕ) : ℝ) := by
    refine le_trans (divDown_le_div _ _ hd0) (le_trans (div_le_div_of_nonneg_right hc hd0.le) ?_)
    rw [div_le_div_iff₀ hd0 hk0]; nlinarith
  have hhi : y / ((i + 2 : ℕ) : ℝ) ≤ toReal (zero : 𝕋) := by
    rw [toReal_zero]; exact div_nonpos_of_nonpos_of_nonneg hy0 hk0.le
  -- `smul_outer` around the power's box
  have hmem := Interval.mem_mat_iff.mp (Interval.smul_outer hlo hhi _
    (MatExp.pow_div_factorial_mem_verifyPowerFloat A (i + 1))) j k
  simp only [Matrix.smul_apply, smul_eq_mul] at hmem
  have heq : Real.MatExp.constCorrTerm (toRealMat A) (toReal r) i j k
      = y / ((i + 2 : ℕ) : ℝ)
        * ((Nat.factorial (i + 1) : ℝ)⁻¹ * (toRealMat A ^ (i + 1)) j k) := by
    rw [Real.MatExp.constCorrTerm, Nat.factorial_succ (i + 1)]
    push_cast
    field_simp
    ring
  rw [heq]
  exact hmem


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expIntegralDiff_mem_verifyCorrectionInputFloat (A : Mat 𝕋 n n) {s : Vec 𝕋 n}
    (hs : ∀ i, 0 < toReal (s i)) {r : 𝕋} (hr : 0 < toReal r) : -- --- CONCL ---
    ∀ p ∈ MatExp.verifyCorrectionInputFloat A s r, ∀ t : ℝ, 0 ≤ t → t ≤ toReal r →
      Real.MatExp.expIntegral (toRealMat A) t
          - (t / toReal r) • Real.MatExp.expIntegral (toRealMat A) (toReal r)
        ∈ p.2.toSet := by -- --- PROOF ---
  rintro ⟨η, G⟩ hG t ht0 htr
  rw [Option.mem_def] at hG
  unfold MatExp.verifyCorrectionInputFloat at hG
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at hG
  obtain ⟨η', hfind, W, hW, rfl, rfl⟩ := hG
  have hη3 : 3 ≤ η' := by
    have hmem := List.mem_of_find?_eq_some hfind
    rw [List.mem_range'_1] at hmem
    omega
  obtain ⟨m, rfl⟩ : ∃ m, η' = m + 2 := ⟨η' - 2, by omega⟩
  -- the real entrywise matrix holds the correction
  have hX := Real.Interval.mem_mat_iff.mp
    (Real.MatExp.expIntegralDiff_mem_constCorrectionMatrixEntrywise (toRealMat A) hr m ht0 htr)
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  obtain ⟨h1, h2⟩ := hX j k
  simp only [Real.MatExp.constCorrectionMatrixEntrywise] at h1 h2
  -- the remainder, the terms and their sums, each in its float bound
  have hWjk := MatExp.expRemainderMat_le_scaledRemainderFloat A hs hr.le m
    W (Option.mem_def.mpr hW) j k
  have hrW : toReal r * Real.MatExp.expRemainderMat (toRealMat A) (toReal r) m j k
      ≤ toReal (mulUp r (W j k)) :=
    le_trans (mul_le_mul_of_nonneg_left hWjk hr.le) (mul_le_mulUp _ _)
  have hterm := fun i : ℕ => MatExp.aux_constCorrTerm_mem A hr.le i j k
  set T := fun i => MatExp.step_verifyConstCorrTermFloat A r i with hT
  obtain ⟨hlo, hhi⟩ := MatExp.verifyCorrSumsFloat_bracket T
    (fun i => Real.MatExp.constCorrTerm (toRealMat A) (toReal r) i j k) j k (fun i => hterm i) m
  simp only [Interval.materialiseMat_eq, show m + 2 - 2 = m from rfl]
  -- the outward rounding of the last addition
  have hsd := subDown_le_sub ((MatExp.verifyCorrSumsFloat ((List.range m).map T)).inf j k)
    (mulUp r (W j k))
  have hau := add_le_addUp ((MatExp.verifyCorrSumsFloat ((List.range m).map T)).sup j k)
    (mulUp r (W j k))
  exact ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
