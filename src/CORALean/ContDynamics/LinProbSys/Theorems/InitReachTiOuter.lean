module

public import CORALean.ContDynamics.LinProbSys.Operations.InitReach
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MulExpIntegral
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContSet.Interval.Real.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Real.Theorems.MemPoint
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContDynamics.LinearSys.Operations.Canonical
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# The time-interval set of `initReach` encloses the mean over the first step

For every mean `x₀` of `Rinit`, every time `t ∈ [0, r]` and every input signal in `B U`, the
mean of the solution at `t`, `e^{At} x₀ + ∫₀ᵗ e^{Aσ}dσ B uTrans + ∫₀ᵗ e^{A(t-s)} u(s) ds`, lies in
the set of `Rfirst.ti` [1]: the deterministic part of `initReach` is an outer enclosure. The proof
is that of the `LinearSys` step, with the constant input folded into the segment: the
interpolation error `M = e^{At} - I - (t/r)(e^{Ar} - I) ∈ F` (`expDiff_mem_correctionMatrix`)
carries `x₀` into `F zonotope(Rinit)` and `B uTrans` into `inputCorr = A⁻¹ F B uTrans`, and
`-Rtrans` there cancels the `Rtrans` of `Rinput`.

What is asked: `A` invertible (CORA divides by it), Taylor order `η ≥ 2` with
`‖Ar‖_∞/(η + 2) < 1` (the remainder bound, `priv_pexpm`'s `epsilon < 1`), `0 ∈ U` (one input
solution for the whole step), and `uTrans = 0` in effect whenever `originContained`, since
the correction is dropped then. Only the means: what this says of the probabilistic zonotope's
law is nothing.

## References

* [1] `contDynamics/@linProbSys/initReach.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace ContSet
open scoped MatrixOrder

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `0` is in every confidence zonotope, its center. -/
theorem LinProbSys.aux_zero_mem_confidenceZonotope (G : Mat ℝ n n) (γ : ℝ) :
    (0 : Vec ℝ n) ∈ (confidenceZonotope G γ).construct :=
  ⟨fun _ => 0, fun _ => by simp, by simp [confidenceZonotope]⟩

/-- A mean of a probabilistic zonotope is in its `γ`-zonotope. -/
theorem LinProbSys.aux_mem_zonotope {P : ProbZonotope n} {x : Vec ℝ n} (hx : x ∈ P.Z.construct)
    (γ : ℝ) : x ∈ (P.zonotope γ).construct := by
  have h := Set.add_mem_add hx (LinProbSys.aux_zero_mem_confidenceZonotope (CFC.sqrt P.cov) γ)
  rw [add_zero, Zonotope.plus_exact] at h
  exact h


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinProbSys.initReach_ti_outer (sys : LinProbSys n m) (Veig : Mat ℝ n n)
    (lambda : Fin n → ℝ) (Rinit : ProbZonotope n) (gammaInit : ℝ) (U : Zonotope (Vec ℝ m))
    (uTrans : Vec ℝ m) {r : ℝ} (hr : 0 < r) {k : ℕ}
    (hε : ‖r • sys.A‖ / (((k + 2 : ℕ) : ℝ) + 2) < 1) (gamma : ℝ) (originContained : Bool)
    (hA : IsUnit sys.A.det) (hoc : originContained = true → sys.B *ᵥ uTrans = 0)
    (h0 : (0 : Vec ℝ m) ∈ U.construct) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ Rinit.Z.construct)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) {w : Vec ℝ n}
    (hw : w ∈ (LinearSys.canonical sys.A : LinearSys ℝ n).inputReach (S := 𝒵)
        (Zonotope.mtimes sys.B U) t) : -- --- STMT ---
    exp (t • sys.A) *ᵥ x₀ + MatExp.expIntegral sys.A t *ᵥ (sys.B *ᵥ uTrans) + w
      ∈ (sys.initReach Veig lambda Rinit gammaInit U uTrans r (k + 2) gamma
          originContained).2.1.Z.construct := by -- --- PROOF ---
  set A := sys.A with hAdef
  set v := sys.B *ᵥ uTrans with hv
  set E := exp (r • A) with hE
  set s := t / r with hs
  set M := exp (t • A) - 1 - s • (E - 1) with hMdef
  set Rtrans := (A⁻¹ * (E - 1)) *ᵥ v with hRtrans
  set F := MatExp.correctionMatrix A r (k + 2) with hF
  have hs0 : 0 ≤ s := div_nonneg ht0 hr.le
  have hs1 : s ≤ 1 := (div_le_one hr).mpr htr
  have hM : M ∈ F.construct := MatExp.expDiff_mem_correctionMatrix A hr hε ht0 htr
  have hx₀γ : x₀ ∈ (Rinit.zonotope gammaInit).construct := LinProbSys.aux_mem_zonotope hx₀ _
  -- the segment from `x₀` towards `e^{Ar} x₀ + Rtrans`, inside `Raux`
  have hz : (E - 1) *ᵥ x₀ + Rtrans ∈ ((Zonotope.mtimes (E - 1) (Rinit.zonotope gammaInit)).plus
      ⟨0, Rtrans, Fin.elim0⟩).construct := by
    rw [← Zonotope.plus_exact, ← Zonotope.mtimes_exact]
    exact Set.add_mem_add (Set.mem_image_of_mem _ hx₀γ) (Zonotope.mem_ofPoint Rtrans)
  have hseg : s • ((E - 1) *ᵥ x₀ + Rtrans) ∈ (Zonotope.linComb ⟨0, 0, Fin.elim0⟩
      ((Zonotope.mtimes (E - 1) (Rinit.zonotope gammaInit)).plus
        ⟨0, Rtrans, Fin.elim0⟩)).construct := by
    refine Zonotope.linComb_outer _ _ ⟨0, Zonotope.mem_ofPoint 0, _, hz, 1 - s,
      ⟨by linarith, by linarith⟩, ?_⟩
    rw [smul_zero, zero_add, sub_sub_cancel]
  have h1 := Set.add_mem_add hx₀ hseg
  rw [Zonotope.plus_exact] at h1
  -- the interpolation error of `x₀`, and of the constant input
  have h2 : M *ᵥ x₀ ∈ (Zonotope.mtimesIntervalMat F (Rinit.zonotope gammaInit)).construct :=
    Zonotope.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hM (Set.mem_image_of_mem _ hx₀γ))
  have h3 : (A⁻¹ * M) *ᵥ v ∈ (if originContained then Zonotope.ofPoint 0
      else Zonotope.mtimesIntervalMat (Interval.matMul (Interval.point A⁻¹) F)
        (Zonotope.ofPoint v)).construct := by
    cases originContained with
    | true =>
      rw [hoc rfl, mulVec_zero]
      exact Zonotope.mem_ofPoint 0
    | false =>
      exact Zonotope.mtimesIntervalMat_outer _ _ (Set.mem_biUnion
        (Interval.matMul_outer _ _ (Interval.mem_point _) hM)
        (Set.mem_image_of_mem _ (Zonotope.mem_ofPoint v)))
  have h4 := Zonotope.mem_ofPoint (-Rtrans)
  -- the time-varying input, in the input solution of the whole step
  have hV0 : (0 : Vec ℝ n) ∈ construct (Zonotope.mtimes sys.B U) := by
    show _ ∈ (Zonotope.mtimes sys.B U).construct
    rw [← Zonotope.mtimes_exact]
    exact ⟨0, h0, mulVec_zero _⟩
  have hw' : w ∈ Zonotope.construct
      ((LinearSys.canonical A : LinearSys ℝ n).inputSolution (S := 𝒵) r (k + 2)
        (Zonotope.mtimes sys.B U)) :=
    LinearSys.inputReach_subset_inputSolution (S := 𝒵) (LinearSys.canonical A) hr (k + 2) hε
    (Zonotope.convex_construct _) (Zonotope.isClosed_construct _)
    (Zonotope.isCompact_construct _).isBounded (Zonotope.convex_construct _)
    (Zonotope.isClosed_construct _) (Zonotope.isCompact_construct _).isBounded
    -- the input reached by `t` is reached by the whole step, `0 ∈ B U` growing it
    (LinearSys.inputReach_mono (S := 𝒵) (LinearSys.canonical A)
      (Zonotope.isCompact_construct _).isBounded hV0 ht0 htr hw)
  have h5 := Set.add_mem_add (Set.add_mem_add (Set.add_mem_add hw' (Zonotope.mem_ofPoint Rtrans))
    (Zonotope.mem_ofPoint (0 : Vec ℝ n)))
    (LinProbSys.aux_zero_mem_confidenceZonotope
      (CFC.sqrt ((0 : Mat ℝ n n) + LinProbSys.inputCov Veig lambda sys.C r)) gamma)
  rw [Zonotope.plus_exact, Zonotope.plus_exact, Zonotope.plus_exact] at h5
  have hall := Set.add_mem_add (Set.add_mem_add (Set.add_mem_add (Set.add_mem_add h1 h2) h3) h4) h5
  rw [Zonotope.plus_exact, Zonotope.plus_exact, Zonotope.plus_exact, Zonotope.plus_exact] at hall
  -- the sum of the pieces is the mean
  have hsum : exp (t • A) *ᵥ x₀ + MatExp.expIntegral A t *ᵥ v + w
      = x₀ + s • ((E - 1) *ᵥ x₀ + Rtrans) + M *ᵥ x₀ + (A⁻¹ * M) *ᵥ v + -Rtrans
        + (w + Rtrans + 0 + 0) := by
    rw [MatExp.expIntegral_eq_inv_mul A hA t, hRtrans, hMdef]
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_add, smul_sub]
    abel
  rw [hsum]
  exact hall

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
