module

public import CORALean.ContDynamics.LinParamSys.Operations.ConstInputSolutionFloat
public import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# `constInputSolutionFloat` holds what a constant input contributes

What the constant `ũ` contributes by any `t ∈ [0, r]` at a member `A` of `sys.A` is
`∫₀ᵗ e^{Aσ}dσ ũ`: the input `ũ` held over `[0, t]` is an admissible input of the segment
`[0, ũ]`, whose contribution grows with time [1, Prop. 3.3] and by `r` lies in
`inputSolutionFloat` [1, Thm. 3.1].

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix ContSet MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The segment `[0, ũ]` holds both of its ends. -/
theorem LinParamSys.aux_zero_mem_segment (uc : Vec 𝕋 n) : -- --- STMT ---
    (0 : Vec ℝ n) ∈ construct (LinComb.linComb
      (OfScalarPoint.ofVec (S := 𝒵[𝕋]) (fun _ : Fin n => (zero : 𝕋)) :
        Zonotope (Vec 𝕋 n))
      (OfScalarPoint.ofVec (S := 𝒵[𝕋]) uc : Zonotope (Vec 𝕋 n))) ∧
    Scalar.toRealVec uc ∈ construct (LinComb.linComb
      (OfScalarPoint.ofVec (S := 𝒵[𝕋]) (fun _ : Fin n => (zero : 𝕋)) :
        Zonotope (Vec 𝕋 n))
      (OfScalarPoint.ofVec (S := 𝒵[𝕋]) uc :
        Zonotope (Vec 𝕋 n))) := by -- --- PROOF ---
  have hz : (0 : Vec ℝ n) ∈ construct
      (OfScalarPoint.ofVec (S := 𝒵[𝕋]) (fun _ : Fin n => (zero : 𝕋)) :
        Zonotope (Vec 𝕋 n)) := by
    have h0 := OfScalarPoint.mem_ofVec (S := 𝒵[𝕋])
      (fun _ : Fin n => (zero : 𝕋))
    rwa [show Scalar.toRealVec (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
  have hu := OfScalarPoint.mem_ofVec (S := 𝒵[𝕋]) uc
  constructor <;> refine LinComb.linComb_outer _ _ ?_
  · exact ⟨0, hz, _, hu, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩
  · exact ⟨0, hz, _, hu, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- What the constant `ũ` contributes by any `t ∈ [0, r]`, at any member `A` of `sys.A`,
lies in `constInputSolutionFloat r η ũ`, at an order admissible for `r`. -/
theorem LinParamSys.expIntegral_mem_constInputSolutionFloat
    (sys : LinParamSys ℐ[𝕋] n) {r : 𝕋} {η : ℕ}
    (hr : 0 < toReal r) (hη : sys.OrderAdmissibleFloat r r η) {A : Mat ℝ n n}
    (hA : A ∈ sys.A.construct) (uc : Vec 𝕋 n) {t : ℝ} (ht0 : 0 ≤ t)
    (htr : t ≤ toReal r) : -- --- STMT ---
    Real.MatExp.expIntegral A t *ᵥ Scalar.toRealVec uc
      ∈ (sys.constInputSolutionFloat r η uc).construct := by -- --- PROOF ---
  obtain ⟨h0seg, hũseg⟩ := LinParamSys.aux_zero_mem_segment uc
  set seg : Zonotope (Vec 𝕋 n) := LinComb.linComb
    (OfScalarPoint.ofVec (S := 𝒵[𝕋]) (fun _ : Fin n => (zero : 𝕋)) :
    Zonotope (Vec 𝕋 n)) (OfScalarPoint.ofVec (S := 𝒵[𝕋]) uc :
      Zonotope (Vec 𝕋 n)) with hseg
  -- the constant `ũ` held over `[0, t]` is an admissible input of the segment
  have hconst : Real.MatExp.expIntegral A t *ᵥ Scalar.toRealVec uc
      ∈ (LinearSys.canonical A : LinearSys ℝ n).inputReach (S := 𝒵[𝕋]) seg t :=
    ⟨fun _ => Scalar.toRealVec uc, fun _ _ => hũseg, aestronglyMeasurable_const,
      (Real.MatExp.expIntegral_constInput A (Scalar.toRealVec uc) ht0).symm⟩
  exact sys.inputReach_subset_inputSolutionFloat hr hη hA seg
    ((LinearSys.canonical A : LinearSys ℝ n).inputReach_mono (CompactSet.isBounded_construct seg)
      h0seg ht0 htr hconst)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
