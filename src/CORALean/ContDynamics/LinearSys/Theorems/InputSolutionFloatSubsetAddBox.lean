module

public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionBoxFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ZeroMemInputTaylorSumFloatError
public import CORALean.ContDynamics.LinearSys.Theorems.ZeroMemIntervalInputRemainder
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatSubsetAddBox
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusSubsetAddBox
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `inputSolutionFloat` reaches no further than the exact input solution, plus a box

The upper side of `inputSolutionFloat`'s outer guarantee, which is what an
inner approximation run in floats needs: the float enclosure lies in the exact
`inputSolution` at `U`'s nominal zonotope, widened by `inputSolutionBoxFloat`.

Order by order, `mtimesIntervalMat_subset_add_box` at the exact `Tᵢ` (a member of
`[Tᵢ]`) writes a point of `[Tᵢ] U` as `Tᵢ (a + e) + b`, `a` in the nominal
zonotope, `e` in `U`'s error box; `Tᵢ e` lies in `[Tᵢ]` applied to that box. The
float sums pay `plus_subset_add_box`. The remainder product is taken through the
zero matrix, which lies in both remainder intervals, so the exact remainder term
holds the `0` its float counterpart is measured against.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic InflatedContSet Matrix
open scoped Pointwise
open scoped CORALean.Real

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Order `i`'s float product lies in the exact `Tᵢ` applied to `U`'s nominal zonotope, widened
by that order's box. -/
theorem aux_inputTerm_subset_add_box (sys : LinearSys 𝕋 n) {r : 𝕋} (hr : 0 ≤ toReal r)
    {U : Zonotope (Vec 𝕋 n)} (hU : (0 : Vec ℝ n) ∈ U.I_error.construct) (i : ℕ) : -- --- CONCL ---
    (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
        (MatExp.intervalInputTerm (Interval.point sys.A) r i) U).construct
      ⊆ (sys.inputTerm (toReal r) i *ᵥ ·) '' ContSet.construct (nominal U)
        + (sys.inputTermBoxFloat r U i).construct := by -- --- PROOF ---
  set IT := MatExp.intervalInputTerm (Interval.point sys.A) r i
  have hT : sys.inputTerm (toReal r) i ∈ IT.construct :=
    MatExp.smul_pow_mem_intervalInputTerm _ hr (Interval.mem_point sys.A) i
  intro x hx
  have hx' : x ∈ (Zonotope.mtimesIntervalMat IT U).construct := by
    have h := hx
    simp only [Mtimes.mtimes, Zonotope.materialise_eq] at h
    exact h
  -- `x = T u + b`, and `u = a + e` with `e` in the error box
  obtain ⟨_, ⟨u, hu, rfl⟩, b, hb, rfl⟩ := Zonotope.mtimesIntervalMat_subset_add_box IT U hU hT hx'
  obtain ⟨a, ha, e, he, rfl⟩ := hu
  have hTe : sys.inputTerm (toReal r) i *ᵥ e ∈
    (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
      IT U.I_error.zonotope).construct :=
    Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) IT _
      (Set.mem_biUnion hT ⟨e, Interval.zonotope_contains _ he, rfl⟩)
  have hb' : b ∈ ContSet.construct (Zonotope.mtimesIntervalMatBox IT U).zonotope :=
    Interval.zonotope_contains _ hb
  refine ⟨sys.inputTerm (toReal r) i *ᵥ a, ⟨a, ha, rfl⟩, sys.inputTerm (toReal r) i *ᵥ e + b,
    Plus.plus_outer _ _ (Set.add_mem_add hTe hb'), ?_⟩
  show _ = sys.inputTerm (toReal r) i *ᵥ (a + e) + b
  rw [Matrix.mulVec_add, add_assoc]

/-- Every partial Taylor sum lies in the exact one at `U`'s nominal zonotope, widened by its
box. -/
theorem aux_inputTaylorSumFloat_subset_add_box (sys : LinearSys 𝕋 n) {r : 𝕋}
    (hr : 0 ≤ toReal r) {U : Zonotope (Vec 𝕋 n)}
    (hU : (0 : Vec ℝ n) ∈ U.I_error.construct) : -- --- CONCL ---
    ∀ i, (sys.inputTaylorSumFloat r U i).construct
      ⊆ ContSet.construct (sys.inputTaylorSum (S := 𝒵)
          (toReal r) (nominal U) i)
        + (sys.inputTaylorSumBoxFloat r U i).construct := by -- --- PROOF ---
  intro i
  induction i with
  | zero =>
    intro x hx
    obtain ⟨y, hy, b, hb, rfl⟩ := aux_inputTerm_subset_add_box sys hr hU 0 hx
    refine ⟨y, ?_, b, hb, rfl⟩
    show y ∈ (Real.Zonotope.mtimes (sys.inputTerm (toReal r) 0) (nominal U)).construct
    rw [← Real.Zonotope.mtimes_exact]
    exact hy
  | succ i ih =>
    -- one more float sum: both summands keep `0` in their error boxes
    set S := sys.inputTaylorSumFloat r U i
    set T := Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
      (MatExp.intervalInputTerm (Interval.point sys.A) r (i + 1)) U
    have hS0 := sys.zero_mem_inputTaylorSumFloat_error hr hU i
    have hT0 : (0 : Vec ℝ n) ∈ T.I_error.construct := by
      show (0 : Vec ℝ n) ∈ ((Zonotope.mtimesIntervalMat _ U).materialise).I_error.construct
      rw [Zonotope.materialise_eq]
      exact Zonotope.zero_mem_mtimesIntervalMat_error
        (MatExp.smul_pow_mem_intervalInputTerm _ hr (Interval.mem_point sys.A) (i + 1)) hU
    intro x hx
    have hx' : x ∈ (S.plus T).construct := by
      have h := hx
      simp only [LinearSys.inputTaylorSumFloat, Plus.plus, Zonotope.materialise_eq] at h
      exact h
    -- the float sum, its two summands, and each summand's own excess
    obtain ⟨_, ⟨s, hs, t, ht, rfl⟩, p, hp, rfl⟩ := Zonotope.plus_subset_add_box S T hS0 hT0 hx'
    obtain ⟨s₀, hs₀, bs, hbs, rfl⟩ := ih hs
    obtain ⟨t₀, ht₀, bt, hbt, rfl⟩ := aux_inputTerm_subset_add_box sys hr hU (i + 1) ht
    have hp' : p ∈ ContSet.construct (Zonotope.plusBox S T).zonotope :=
      Interval.zonotope_contains _ hp
    refine ⟨s₀ + t₀, ?_, bs + bt + p, ?_, by dsimp only; abel⟩
    · show s₀ + t₀ ∈ ((sys.inputTaylorSum (S := 𝒵) (toReal r)
        (nominal U) i).plus (Real.Zonotope.mtimes (sys.inputTerm (toReal r) (i + 1))
          (nominal U))).construct
      rw [← Real.Zonotope.plus_exact, ← Real.Zonotope.mtimes_exact]
      exact Set.add_mem_add hs₀ ht₀
    · exact Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _ (Set.add_mem_add hbs hbt))
        hp')


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float input solution is *contained in* the exact `inputSolution` at `U`'s nominal
zonotope, widened by `inputSolutionBoxFloat` — the upper side of its outer guarantee. -/
theorem LinearSys.inputSolutionFloat_subset_add_box (sys : LinearSys 𝕋 n) {r : 𝕋}
    (hr : 0 ≤ toReal r) {η : ℕ} (hη : sys.OrderAdmissibleFloat r r η) {U : Zonotope (Vec 𝕋 n)}
    (hU : (0 : Vec ℝ n) ∈ U.I_error.construct) : -- --- CONCL ---
    (sys.inputSolutionFloat r η U).construct
      ⊆ ContSet.construct (sys.inputSolution (S := 𝒵)
          (toReal r) η (nominal U))
        + (sys.inputSolutionBoxFloat r η U).construct := by -- --- PROOF ---
  set S := sys.inputTaylorSumFloat r U η
  set Rm := MatExp.intervalInputRemainder (Interval.point sys.A) r η
  set F := Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋]) Rm U
  have h0 := sys.zero_mem_intervalInputRemainder hr hη
  have hF0 : (0 : Vec ℝ n) ∈ F.I_error.construct := by
    show (0 : Vec ℝ n) ∈ ((Zonotope.mtimesIntervalMat _ U).materialise).I_error.construct
    rw [Zonotope.materialise_eq]
    exact Zonotope.zero_mem_mtimesIntervalMat_error h0 hU
  -- the exact remainder term holds `0`: the zero matrix is in its interval
  have hA : Scalar.toRealMat sys.A ∈ (Interval.point sys.A).construct := Interval.mem_point sys.A
  have hε : ‖toReal r • Scalar.toRealMat sys.A‖ / ((η : ℝ) + 2) ≤ 1 / 2 :=
    le_trans (by gcongr; exact MatExp.norm_smul_le_normUpperBound _ r hA) hη.2
  have hE0 := Real.MatExp.expRemainderBound_nonneg η hε
  have hR0 : (0 : Mat ℝ n n) ∈
      (Real.MatExp.inputRemainder (Scalar.toRealMat sys.A) (toReal r) η).construct :=
    Real.Interval.mem_mat_iff.mpr fun _ _ =>
      ⟨neg_nonpos.mpr (mul_nonneg hr hE0), mul_nonneg hr hE0⟩
  have hRem : (0 : Vec ℝ n) ∈ (Real.Zonotope.mtimesIntervalMat (Real.MatExp.inputRemainder
      (Scalar.toRealMat sys.A) (toReal r) η) (nominal U)).construct := by
    have h := Real.Zonotope.mtimesIntervalMat_outer _ (nominal U)
      (Set.mem_biUnion hR0 ⟨_, Real.Zonotope.center_mem_construct (nominal U), rfl⟩)
    simpa only [Matrix.zero_mulVec] using h
  -- the float sum, then the Taylor sum and the remainder product, each against its exact part
  intro x hx
  have hx' : x ∈ (S.plus F).construct := by
    have h := hx
    simp only [LinearSys.inputSolutionFloat, Plus.plus, Zonotope.materialise_eq] at h
    exact h
  obtain ⟨_, ⟨s, hs, f, hf, rfl⟩, p, hp, rfl⟩ :=
    Zonotope.plus_subset_add_box S F (sys.zero_mem_inputTaylorSumFloat_error hr hU η) hF0 hx'
  obtain ⟨s₀, hs₀, bs, hbs, rfl⟩ := aux_inputTaylorSumFloat_subset_add_box sys hr hU η hs
  have hf' : f ∈ (Zonotope.mtimesIntervalMat Rm U).construct := by
    have h := hf
    simp only [F, Mtimes.mtimes, Zonotope.materialise_eq] at h
    exact h
  obtain ⟨_, ⟨u, -, rfl⟩, bf, hbf, rfl⟩ := Zonotope.mtimesIntervalMat_subset_add_box Rm U hU h0 hf'
  -- the boxes, read as zonotopes and summed
  have hp' : p ∈ ContSet.construct (Zonotope.plusBox S F).zonotope :=
    Interval.zonotope_contains _ hp
  have hbf' : bf ∈ ContSet.construct (Zonotope.mtimesIntervalMatBox Rm U).zonotope :=
    Interval.zonotope_contains _ hbf
  refine ⟨s₀ + 0, ?_, bs + bf + p, ?_, ?_⟩
  · show s₀ + 0 ∈ ((sys.inputTaylorSum (S := 𝒵) (toReal r)
      (nominal U) η).plus (Real.Zonotope.mtimesIntervalMat
        (Real.MatExp.inputRemainder (Scalar.toRealMat sys.A) (toReal r) η) (nominal U))).construct
    rw [← Real.Zonotope.plus_exact]
    exact Set.add_mem_add hs₀ hRem
  · exact Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _ (Set.add_mem_add hbs hbf'))
      hp')
  · show s₀ + 0 + (bs + bf + p) = s₀ + bs + ((0 : Mat ℝ n n) *ᵥ u + bf) + p
    rw [Matrix.zero_mulVec]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
