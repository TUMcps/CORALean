module

public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepErrorBoxFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepExcessFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionFloatSubsetAddBox
public import CORALean.ContDynamics.LinearSys.Theorems.ZeroMemInputSolutionFloatError
public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionSubsetConstInputAddErrorBox
public import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepErrorBoxSubsetFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# A float step reaches no further than the exact held-input step, plus two boxes

The upper side of the float step `timePointStepInputFloat`: a point of it is
`e^{Ar} x + (∫₀^r e^{As} ds) u`, for `x` in the float `X` and `u` in `U`'s
nominal zonotope, plus a point of `timePointStepExcessFloat` and one of
`timePointStepErrorBoxFloat`. Three bounds compose:

* `mtimesIntervalMat_subset_add_box`, at the true `e^{Ar}`, a member of
  `[e^{Ar}]` by `exp_mem_expIntervalFloat`;
* `plus_subset_add_box`, and `inputSolutionFloat_subset_add_box`;
* `inputSolution_subset_constInput_add_errorBox`, the exact input solution
  against the held input, whose error box `timePointStepErrorBox_subset_float`
  puts inside the float one.

`e^{Ar} X` is the image of the float `X`'s whole `construct`; a caller splits it
further (`X`'s nominal part, and its error box carried by `[e^{Ar}]`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic InflatedContSet Matrix NormedSpace
open scoped Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float step is *contained in* `e^{Ar} X` plus the held-input contribution of `U`'s
nominal zonotope, widened by `timePointStepExcessFloat` and the step's float error box — the
upper side of the float step, at `r > 0` and an admissible order. -/
theorem LinearSys.timePointStepInputFloat_subset_add_excess (sys : LinearSys 𝕋 n) {r : 𝕋}
    (hr : 0 < toReal r) {η : ℕ} (hη : sys.OrderAdmissibleFloat r r η) {X U : Zonotope (Vec 𝕋 n)}
    (hX : (0 : Vec ℝ n) ∈ X.I_error.construct)
    (hU : (0 : Vec ℝ n) ∈ U.I_error.construct) : -- --- STMT ---
    (sys.timePointStepInputFloat r η X U).construct
      ⊆ (exp (toReal r • Scalar.toRealMat sys.A) *ᵥ ·) '' X.construct
        + (Real.Zonotope.mtimes (Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal r))
            (nominal U)).construct
        + (sys.timePointStepExcessFloat r η X U).construct
        + (sys.timePointStepErrorBoxFloat r η U).construct := by -- --- PROOF ---
  set eA := sys.expIntervalFloat r r η
  set M := Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋]) eA X
  set P := sys.inputSolutionFloat r η U
  have he := sys.exp_mem_expIntervalFloat hη (t := toReal r) le_rfl le_rfl
  have hM0 : (0 : Vec ℝ n) ∈ M.I_error.construct := by
    show (0 : Vec ℝ n) ∈ ((Zonotope.mtimesIntervalMat _ X).materialise).I_error.construct
    rw [Zonotope.materialise_eq]
    exact Zonotope.zero_mem_mtimesIntervalMat_error he hX
  have hP0 := sys.zero_mem_inputSolutionFloat_error hr.le hη hU
  -- the order bound the exact input solution's theorem asks for
  have hA : Scalar.toRealMat sys.A ∈ (Interval.point sys.A).construct := Interval.mem_point sys.A
  have hε : ‖toReal r • Scalar.toRealMat sys.A‖ / ((η : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (le_trans (by gcongr; exact MatExp.norm_smul_le_normUpperBound _ r hA) hη.2)
      (by norm_num)
  intro x hx
  have hx' : x ∈ (M.plus P).construct := by
    have h := hx
    simp only [LinearSys.timePointStepInputFloat, Plus.plus, Zonotope.materialise_eq] at h
    exact h
  -- the sum, the product, the float input solution and the exact one, peeled in turn
  obtain ⟨_, ⟨m, hm, q, hq, rfl⟩, p, hp, rfl⟩ := Zonotope.plus_subset_add_box M P hM0 hP0 hx'
  have hm' : m ∈ (Zonotope.mtimesIntervalMat eA X).construct := by
    have h := hm
    simp only [M, Mtimes.mtimes, Zonotope.materialise_eq] at h
    exact h
  obtain ⟨_, ⟨y, hy, rfl⟩, b₁, hb₁, rfl⟩ := Zonotope.mtimesIntervalMat_subset_add_box eA X hX he hm'
  obtain ⟨s, hs, b₂, hb₂, rfl⟩ := sys.inputSolutionFloat_subset_add_box hr.le hη hU hq
  obtain ⟨w, hw, t, ht, rfl⟩ :=
    sys.inputSolution_subset_constInput_add_errorBox hr η hε (nominal U) hs
  have ht' := sys.timePointStepErrorBox_subset_float hr.le hη U ht
  -- the three float boxes, read as zonotopes and summed
  have hb₁' : b₁ ∈ ContSet.construct (Zonotope.mtimesIntervalMatBox eA X).zonotope :=
    Interval.zonotope_contains _ hb₁
  have hp' : p ∈ ContSet.construct (Zonotope.plusBox M P).zonotope :=
    Interval.zonotope_contains _ hp
  have hex : b₁ + p + b₂ ∈ (sys.timePointStepExcessFloat r η X U).construct :=
    Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _ (Set.add_mem_add hb₁' hp')) hb₂)
  refine ⟨_, ⟨_, ⟨_, ⟨y, hy, rfl⟩, w, hw, rfl⟩, _, hex, rfl⟩, t, ht', ?_⟩
  dsimp only
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
