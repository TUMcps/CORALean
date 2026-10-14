module

public import CORALean.ContDynamics.LinProbSys.Operations.InitReach
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MulExpIntegral
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# The time-point set of `initReach` encloses the mean at the end of the first step

For every mean `x₀` of `Rinit` and every input signal in `B U`, the mean of the solution at
`r`, `e^{Ar} x₀ + ∫₀ʳ e^{Aσ}dσ B uTrans + ∫₀ʳ e^{A(r-s)} u(s) ds`, lies in the set of
`Rfirst.tp = eAt Rinit + zonotope(Rpar)` [1]. At the end of the step neither `0 ∈ U` nor the
correction `inputCorr` is needed, `A` invertible still is (CORA divides by it). Only the means,
as for `initReach_ti_outer`.

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinProbSys.initReach_tp_outer (sys : LinProbSys n m) (Veig : Mat ℝ n n)
    (lambda : Fin n → ℝ) (Rinit : ProbZonotope n) (gammaInit : ℝ) (U : Zonotope (Vec ℝ m))
    (uTrans : Vec ℝ m) {r : ℝ} (hr : 0 < r) {η : ℕ}
    (hε : ‖r • sys.A‖ / ((η : ℝ) + 2) < 1) (gamma : ℝ) (originContained : Bool)
    (hA : IsUnit sys.A.det) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ Rinit.Z.construct) {w : Vec ℝ n}
    (hw : w ∈ (⟨sys.A⟩ : LinearSys ℝ n).inputReach (S := 𝒵) (Zonotope.mtimes sys.B U) r) :
    exp (r • sys.A) *ᵥ x₀ + MatExp.expIntegral sys.A r *ᵥ (sys.B *ᵥ uTrans) + w
      ∈ (sys.initReach Veig lambda Rinit gammaInit U uTrans r η gamma
          originContained).1.Z.construct := by -- --- PROOF ---
  set A := sys.A with hAdef
  set v := sys.B *ᵥ uTrans with hv
  set Rtrans := (A⁻¹ * (exp (r • A) - 1)) *ᵥ v with hRtrans
  -- `e^{Ar} x₀` in `eAt Rinit`
  have h1 : exp (r • A) *ᵥ x₀ ∈ (Zonotope.mtimes (exp (r • A)) Rinit.Z).construct := by
    rw [← Zonotope.mtimes_exact]
    exact Set.mem_image_of_mem _ hx₀
  -- the input, in the input solution, and the constant input's `Rtrans`
  have hw' : w ∈ Zonotope.construct ((⟨A⟩ : LinearSys ℝ n).inputSolution (S := 𝒵) r η
      (Zonotope.mtimes sys.B U)) := LinearSys.inputReach_subset_inputSolution (S := 𝒵) ⟨A⟩ hr η
    hε (Zonotope.convex_construct _) (Zonotope.isClosed_construct _)
    (Zonotope.isCompact_construct _).isBounded (Zonotope.convex_construct _)
    (Zonotope.isClosed_construct _) (Zonotope.isCompact_construct _).isBounded hw
  have h5 := Set.add_mem_add (Set.add_mem_add (Set.add_mem_add hw' (Zonotope.mem_ofPoint Rtrans))
    (Zonotope.mem_ofPoint (0 : Vec ℝ n)))
    (show (0 : Vec ℝ n) ∈ (confidenceZonotope
      (CFC.sqrt ((0 : Mat ℝ n n) + LinProbSys.inputCov Veig lambda sys.C r)) gamma).construct from
      ⟨fun _ => 0, fun _ => by simp, by simp [confidenceZonotope]⟩)
  rw [Zonotope.plus_exact, Zonotope.plus_exact, Zonotope.plus_exact] at h5
  have hall := Set.add_mem_add h1 h5
  rw [Zonotope.plus_exact] at hall
  have hsum : exp (r • A) *ᵥ x₀ + MatExp.expIntegral A r *ᵥ v + w
      = exp (r • A) *ᵥ x₀ + (w + Rtrans + 0 + 0) := by
    rw [MatExp.expIntegral_eq_inv_mul A hA r, hRtrans]
    abel
  rw [hsum]
  exact hall

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
