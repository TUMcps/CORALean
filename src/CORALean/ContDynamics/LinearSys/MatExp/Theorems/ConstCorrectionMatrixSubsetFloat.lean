module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrixFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsCorrCoeffLeOne
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffLowFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormSmulLeNormUpperBoundFloat

@[expose] public section

/-!
# The exact `G` of every member lies in the float `G`

`Real.MatExp.constCorrectionMatrix`, the constant input's correction matrix at a matrix `M` of
the box `A`, entry by entry inside `MatExp.intervalConstCorrectionMatrix A`: each order is
inside its float term (`aux_constCorrTerm_mem_intervalConstCorrTerm`), `sumDown_le_sum` and
`sum_le_sumUp` carry the orders through the rounded sums, and `expRemainderBound_le` the
remainder `r E(r M)`. `hε` asks `1/2`, as the float remainder bound does. At the point box
`Interval.point A` this is the float `[G]` of `oneStep`.

## Inputs
* `A` – float interval matrix
* `r` – float step length
* `η` – Taylor order
* `M` – member matrix

## Hypotheses
* `hr` – step length nonnegative
* `hε` – float norm bound small enough for the Taylor order
* `hM` – member lies in the interval matrix

## Conclusion
* the exact integrated correction of the member lies in the float one
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every member's integrated correction term lies in the float box. -/
private theorem MatExp.aux_constCorrTerm_mem_intervalConstCorrTerm (A : Interval (Mat 𝕋 n n))
    {r : 𝕋} (hr : 0 ≤ toReal r) (i : ℕ) {M : Mat ℝ n n} (hM : M ∈ A.construct)
    (j k : Fin n) : -- --- CONCL ---
    toReal ((MatExp.intervalConstCorrTerm A r i).inf j k)
        ≤ Real.MatExp.constCorrTerm M (toReal r) i j k
      ∧ Real.MatExp.constCorrTerm M (toReal r) i j k
        ≤ toReal ((MatExp.intervalConstCorrTerm A r i).sup j k) := by -- --- PROOF ---
  obtain ⟨-, hhi⟩ := MatExp.taylorCoeffBounds_mem hr (i + 2)
  set ρ := toReal r ^ (i + 2) / (Nat.factorial (i + 2) : ℝ)
  have hρ : 0 ≤ ρ := by positivity
  have hκ := MatExp.corrCoeffLow_le (𝕋 := 𝕋) (show 2 ≤ i + 2 by omega)
  have hc0 : Real.MatExp.corrCoeff (i + 2) ≤ 0 := by
    have h := Real.MatExp.corrCoeff_le_sub (show 2 ≤ i + 2 by omega) (le_refl (0:ℝ))
    rwa [zero_pow (by omega : i + 2 ≠ 0), sub_zero] at h
  -- the lower end: a nonpositive `κ` against the upper end of the nonnegative scalar
  have hlo : toReal (mulDown (MatExp.corrCoeffLow (𝕋 := 𝕋) (i + 2))
        (MatExp.taylorCoeffBounds r (i + 2)).sup)
      ≤ Real.MatExp.corrCoeff (i + 2) * ρ :=
    le_trans (mulDown_le_mul _ _) (le_trans
      (mul_le_mul_of_nonpos_left hhi (le_trans hκ hc0))
      (mul_le_mul_of_nonneg_right hκ hρ))
  have hhi' : Real.MatExp.corrCoeff (i + 2) * ρ ≤ toReal (zero : 𝕋) := by
    rw [toReal_zero]; exact mul_nonpos_of_nonpos_of_nonneg hc0 hρ
  -- `smul_outer` and `matPow_outer` put the entry in the float box
  have hmem := Real.Interval.mem_mat_iff.mp
    (Interval.smul_outer hlo hhi' _ (Interval.matPow_outer A hM (i + 1))) j k
  simp only [Interval.nominal, RealImage.realImage, toRealMat, Matrix.smul_apply,
    smul_eq_mul] at hmem
  have heq : Real.MatExp.constCorrTerm M (toReal r) i j k
      = Real.MatExp.corrCoeff (i + 2) * ρ * (M ^ (i + 1)) j k := by
    rw [Real.MatExp.constCorrTerm]; ring
  rw [heq, MatExp.intervalConstCorrTerm, Interval.materialiseMat_eq]
  exact hmem


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.constCorrectionMatrix_subset_intervalConstCorrectionMatrix
    (A : Interval (Mat 𝕋 n n)) {r : 𝕋} (hr : 0 ≤ toReal r) (η : ℕ)
    (hε : toReal (MatExp.normUpperBound (Interval.smul r r A)) / ((η : ℝ) + 2) ≤ 1 / 2)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) : -- --- CONCL ---
    (Real.MatExp.constCorrectionMatrix M (toReal r) η).construct
      ⊆ (MatExp.intervalConstCorrectionMatrix A r η).construct := by -- --- PROOF ---
  have hnorm := MatExp.norm_smul_le_normUpperBound A r hM
  have hE := MatExp.expRemainderBound_le η hnorm (le_trans (norm_nonneg _) hnorm) hε
  intro X hX
  have hX' := Real.Interval.mem_mat_iff.mp hX
  refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
  obtain ⟨h1, h2⟩ := hX' j k
  simp only [Real.MatExp.constCorrectionMatrix] at h1 h2
  have hterm := fun i : ℕ => MatExp.aux_constCorrTerm_mem_intervalConstCorrTerm A hr i hM j k
  -- the stored orders, rounded and summed, bracket the exact sums
  have hlo : toReal (sumDown fun i : Fin η =>
        minimum ((MatExp.intervalConstCorrTerm A r i).inf j k) zero)
      ≤ ∑ i ∈ Finset.range η, min (Real.MatExp.constCorrTerm M (toReal r) i j k) 0 := by
    refine le_trans (sumDown_le_sum _) ?_
    rw [← Fin.sum_univ_eq_sum_range (fun i => min (Real.MatExp.constCorrTerm M _ i j k) 0)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [toReal_minimum, toReal_zero]
    exact min_le_min_right _ (hterm i).1
  -- and the same from above
  have hhi : ∑ i ∈ Finset.range η, max (Real.MatExp.constCorrTerm M (toReal r) i j k) 0
      ≤ toReal (sumUp fun i : Fin η =>
        maximum ((MatExp.intervalConstCorrTerm A r i).sup j k) zero) := by
    refine le_trans ?_ (sum_le_sumUp _)
    rw [← Fin.sum_univ_eq_sum_range (fun i => max (Real.MatExp.constCorrTerm M _ i j k) 0)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [toReal_maximum, toReal_zero]
    exact max_le_max_right _ (hterm i).2
  -- the tail `r E(r)` and the rounded sums bracket the exact entry
  set E := MatExp.expRemainderBound (MatExp.normUpperBound (Interval.smul r r A)) η
  have hrE : toReal r * Real.MatExp.expRemainderBound (toReal r • M) η ≤ toReal (mulUp r E) :=
    le_trans (mul_le_mul_of_nonneg_left hE hr) (mul_le_mulUp _ _)
  set sLo := sumDown fun i : Fin η =>
    minimum ((MatExp.intervalConstCorrTerm A r i).inf j k) zero
  set sHi := sumUp fun i : Fin η =>
    maximum ((MatExp.intervalConstCorrTerm A r i).sup j k) zero
  simp only [MatExp.intervalConstCorrectionMatrix, Interval.materialiseMat_eq, Interval.nominal,
    RealImage.realImage, toRealMat, Fin.getElem_fin, Vector.getElem_ofFn]
  show toReal (subDown sLo (mulUp r E)) ≤ _ ∧ _ ≤ toReal (addUp sHi (mulUp r E))
  have hsd := subDown_le_sub sLo (mulUp r E)
  have hau := add_le_addUp sHi (mulUp r E)
  exact ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
