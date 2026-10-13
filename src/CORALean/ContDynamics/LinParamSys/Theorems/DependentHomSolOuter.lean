module

public import CORALean.ContDynamics.LinParamSys.Operations.DependentHomSol
public import CORALean.ContDynamics.LinParamSys.Theorems.MemDependentLowOrder
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosure
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylorTail
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundMono
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.InputIntervalTaylorTail
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputRemainder
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpIntegralSubTaylorLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContSet.Interval.Real.Theorems.MemMat
public import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
public import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Real.Theorems.SmulOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem

@[expose] public section

/-!
# The corrected `priv_dependentHomSol` holds the solution at the end of the step

`LinParamSys.dependentHomSol_outer`: for every parameter `p ∈ [-1, 1]ᵏ`, shared by the system
matrix `A(p) = A_c + Σ pᵢ A_g⁽ⁱ⁾` and the constant input `u(p) = U_c + Σ pᵢ U_G⁽ⁱ⁾`, and every
`x₀ ∈ Rinit`, the solution `e^{A(p) r} x₀ + ∫₀ʳ e^{A(p)(r-s)} u(p) ds` lies in
`dependentHomSol r η Rinit U_c U_G`.

The solution splits as the parts do: `e^{Ar}(x₀ - c)` (the box's exponential, `R_hom_state`),
the time orders up to `A²` from `c` and of `u` (`mem_dependentLowOrder`, `R_lowOrder`), orders
`3 … η` of both (`taylorTail_mem_expIntervalTaylorTail`, `inputTail_mem_inputIntervalTaylorTail`)
and what is past `η` (`norm_exp_sub_expTaylor_le`, `norm_expIntegral_sub_taylor_le`), `R_rem`.

`hε` is CORA's convergence condition `‖A r‖_∞/(η + 2) < 1`, at the box of `A r`; `η = m + 2`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The solution at the end of the step, at every shared parameter and initial state. -/
theorem LinParamSys.dependentHomSol_outer (sys : LinParamSys 𝕄𝒵 n) {r : ℝ} (hr : 0 < r)
    {m : ℕ} (hε : ‖(Interval.smul r sys.A.interval).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (Rinit : Zonotope (Vec ℝ n)) (Uc : Vec ℝ n) (UG : Fin sys.A.h → Vec ℝ n)
    {p : Fin sys.A.h → ℝ} (hp : ∀ i, |p i| ≤ 1) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct Rinit) :
    let A := sys.A.c + ∑ i, p i • sys.A.G i
    let u := Uc + ∑ i, p i • UG i
    exp (r • A) *ᵥ x₀ + ∫ s in (0:ℝ)..r, exp ((r - s) • A) *ᵥ u
      ∈ construct (sys.dependentHomSol r (m + 2) Rinit Uc UG) := by -- --- PROOF ---
  intro A u
  set η := m + 2 with hη
  set c := Rinit.c with hc
  set Ar := Interval.smul r sys.A.interval with hAr
  -- the member, in the matrix zonotope and in its box
  have hAZ : A ∈ construct sys.A := ⟨p, hp, rfl⟩
  have hAbox : A ∈ sys.A.interval.construct := Zonotope.interval_contains _ hAZ
  have hrA : r • A ∈ Ar.construct := Interval.smul_outer r _ hAbox
  have hεA : ‖r • A‖ / ((η : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (by gcongr; exact Interval.norm_le_absMax hrA) hε
  rw [MatExp.expIntegral_constInput A u hr.le]
  -- the orders kept, those past two up to `η`, and the remainders
  set T₂ := MatExp.expTaylor (r • A) 2 with hT₂
  set Ts := ∑ i ∈ Finset.Ico 3 (η + 1), ((Nat.factorial i : ℝ)⁻¹) • (r • A) ^ i with hTs
  set Rs := exp (r • A) - MatExp.expTaylor (r • A) η with hRs
  set S₂ := ∑ i ∈ Finset.range 3, ((Nat.factorial (i + 1) : ℝ)⁻¹ * r ^ (i + 1)) • A ^ i
    with hS₂
  set Tu := ∑ i ∈ Finset.Ico 3 (η + 1), (r / (Nat.factorial (i + 1) : ℝ)) • (r • A) ^ i
    with hTu
  set Ru := MatExp.expIntegral A r
    - ∑ i ∈ Finset.range (η + 1), ((Nat.factorial (i + 1) : ℝ)⁻¹ * r ^ (i + 1)) • A ^ i
    with hRu
  -- the exponential and its integral, split at orders two and `η`
  have hexp : exp (r • A) = T₂ + Ts + Rs := by
    rw [hRs, MatExp.expTaylor, ← Finset.sum_range_add_sum_Ico _ (by omega : 3 ≤ η + 1)]
    simp only [hT₂, MatExp.expTaylor, hTs]
    abel
  have hint : MatExp.expIntegral A r = S₂ + Tu + Ru := by
    have hIco : ∑ i ∈ Finset.Ico 3 (η + 1), ((Nat.factorial (i + 1) : ℝ)⁻¹ * r ^ (i + 1)) • A ^ i
        = Tu := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_pow, smul_smul]
      congr 1
      rw [pow_succ]; ring
    rw [hRu, ← Finset.sum_range_add_sum_Ico _ (by omega : 3 ≤ η + 1), hIco]
    abel
  -- the kept orders, in the form `mem_dependentLowOrder` reads
  have hlow : T₂ *ᵥ c + S₂ *ᵥ u
      = c + r • (A *ᵥ c) + (r ^ 2 / 2) • (A *ᵥ (A *ᵥ c))
        + (r • u + (r ^ 2 / 2) • (A *ᵥ u) + (r ^ 3 / 6) • (A *ᵥ (A *ᵥ u))) := by
    simp only [hT₂, hS₂, MatExp.expTaylor, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, Matrix.add_mulVec, Matrix.smul_mulVec, smul_pow, pow_zero, pow_one, sq,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Nat.factorial, Nat.cast_one]
    module
  have hsplit : exp (r • A) *ᵥ x₀ + MatExp.expIntegral A r *ᵥ u
      = (exp (r • A) *ᵥ (x₀ + -c) + (T₂ *ᵥ c + S₂ *ᵥ u))
        + ((Ts + Rs) *ᵥ c + (Tu + Ru) *ᵥ u) := by
    have hx : exp (r • A) *ᵥ x₀ = exp (r • A) *ᵥ (x₀ + -c) + exp (r • A) *ᵥ c := by
      rw [Matrix.mulVec_add, Matrix.mulVec_neg]; abel
    rw [hx]
    nth_rewrite 2 [hexp]
    rw [hint]
    simp only [Matrix.add_mulVec]
    abel
  rw [hsplit]
  refine Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_))
    (Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)))
  · -- `R_hom_state`: the box's exponential on `Rinit - c`
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
      (MatExp.exp_mem_expIntervalEnclosure _ η hrA hε) (Set.mem_image_of_mem _
        (Plus.plus_outer _ _ (Set.add_mem_add hx₀ (Zonotope.mem_ofPoint _)))))
  · -- `R_lowOrder`: the dependent orders, exactly
    rw [hlow]
    exact LinParamSys.mem_dependentLowOrder _ _ _ _ _ _ hp
  · -- `R_rem_state`: orders `3 … η` by interval arithmetic, `E` past them
    have hTsm := MatExp.taylorTail_mem_expIntervalTaylorTail Ar hrA η
    have hRsle : ∀ i j, |Rs i j| ≤ MatExp.expRemainderBound Ar.absMax η := fun i j =>
      calc |Rs i j| ≤ ‖Rs‖ := abs_entry_le_norm _ i j
        _ ≤ MatExp.expRemainderBound (r • A) η := norm_exp_sub_expTaylor_le _ η hεA
        _ ≤ MatExp.expRemainderBound Ar.absMax η :=
          MatExp.expRemainderBound_mono η (Interval.norm_le_absMax hrA) hε
    refine Mtimes.mtimes_outer _ _ (Set.mem_biUnion ?_
      (Set.mem_image_of_mem _ (Zonotope.mem_ofPoint c)))
    refine Interval.mem_mat_iff.mpr fun i j => ?_
    have h1 := Interval.mem_mat_iff.mp hTsm i j
    have h2 := abs_le.mp (hRsle i j)
    simp only [Matrix.add_apply]
    exact ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
  · -- `R_rem_input`: the input's orders `3 … η`, and `E r` past them
    have hTum := MatExp.inputTail_mem_inputIntervalTaylorTail Ar r hrA η
    have hRum : Ru ∈ (MatExp.inputRemainder A r η).construct := by
      have hle := MatExp.norm_expIntegral_sub_taylor_le A hr.le η hεA
      refine Interval.mem_mat_iff.mpr fun i j => ?_
      have h := abs_le.mp ((abs_entry_le_norm Ru i j).trans hle)
      exact ⟨h.1, h.2⟩
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
      (Interval.plus_outer _ _ (Set.add_mem_add hTum
        (MatExp.intervalInputRemainder_contains _ hr η hε hAbox hRum)))
      (Set.mem_image_of_mem _ ⟨p, hp, rfl⟩))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
