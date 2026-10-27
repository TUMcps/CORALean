module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachMu
public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachTimeInterval
public import CORALean.ContSet.Capsule.Real.Operations.SupportBound
public import CORALean.ContSet.Capsule.Real.Theorems.CenterMemConstructIff
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.HPolytope.Real.Operations.Comap
public import CORALean.ContSet.HPolytope.Real.Operations.MapEquiv
public import CORALean.ContSet.HPolytope.Real.Operations.MinkDiffOf
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.IsBoundedDropEqsMinkDiffOf
public import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Real.Operations.SupportBound
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Alg. 3`: the EA time-interval backward reachable set, every line

[1, Alg. 3] in full. Lines 3-5 compute the two polytopes of the inner approximated homogeneous
time-interval solution (21): `box(X_end)` from the caller's support oracle `ρ` (the linear
programs of (9)), `F box(X_end)` with `F` the interval matrix (19), `μ` (22) at the spectral norm,
`P₁ = X_end ⊖ F box(X_end) ⊖ B_μ` and `P₂ = e^{AΔt}X_end ⊖ F box(X_end) ⊖ B_μ`, `e^{AΔt}X_end` the
image of the halfspace description under the invertible `e^{AΔt}`. Lines 1-2 and 6-14 are
`maxBackReachTimeInterval`, which takes the two polytopes. Line 14's union is no constrained
zonotope, so the result is a `Set`. `Zw` is (27), the constant center trajectory's contribution.
`ρ` answers for bounded polytopes only; the rows of `X_end` bound it, which erosion and map keep.

## Inputs
* `sys` – linear system
* `ρ` – support oracle for bounded polytopes
* `Xend` – target polytope
* `U` – input zonotope
* `W₀` – initial disturbance zonotope
* `Zw` – center trajectory contribution
* `t₀` – start time
* `tend` – end time
* `η` – Taylor order
* `ω` – number of iterations

## Hypotheses
* `hXend` – the inequality rows of `Xend` bound it

## Output
* union of the inner approximated time-interval backward reachable sets
## References

* [1] [M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control,
      2026.](../../../../../references/2026/wetzlinger-tac-backward-reachability.md)
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5
-- Written:       08-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `e^{AΔt}` as a linear equivalence, `e^{-AΔt}` its inverse. -/
@[step_of LinearSys.maxBackReach]
noncomputable def step_maxBackReach_expEquiv (A : Mat ℝ n n) (Δt : ℝ) : Vec ℝ n ≃ₗ[ℝ] Vec ℝ n :=
  LinearEquiv.ofLinear (exp (Δt • A)).mulVecLin (exp (-(Δt • A))).mulVecLin
    (by
      have h : exp (Δt • A) * exp (-(Δt • A)) = 1 := by
        rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl (Δt • A))),
          add_neg_cancel, exp_zero]
      rw [← Matrix.mulVecLin_mul, h, Matrix.mulVecLin_one])
    (by
      have h : exp (-(Δt • A)) * exp (Δt • A) = 1 := by
        rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl (Δt • A))),
          neg_add_cancel, exp_zero]
      rw [← Matrix.mulVecLin_mul, h, Matrix.mulVecLin_one])

/-- Lines 4-5: `X ⊖ F box(X_end) ⊖ B_μ`, one of the two polytopes of the inner
approximated homogeneous time-interval solution (21). -/
@[step_of LinearSys.maxBackReach]
noncomputable def LinearSys.step_maxBackReachPoly (X : HPolytope (Vec ℝ n))
    (FB : Zonotope (Vec ℝ n)) (μ : ℝ) : HPolytope (Vec ℝ n) :=
  let XF := X.minkDiffOf FB.construct fun i => FB.supportBound (X.A i)  -- ⊖ F box(X_end)
  XF.minkDiffOf (⟨0, 0, μ⟩ : Capsule n).construct                       -- ⊖ B_μ
    fun i => (⟨0, 0, μ⟩ : Capsule n).supportBound (XF.A i)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: `R̂^{∃∀}(-τ)` from the target set `X_end`, lines 3-5 computed here. -/
noncomputable def LinearSys.maxBackReach (sys : LinearSys 𝕋 n)
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (_ : Bornology.IsBounded P.construct)
      (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (Xend : HPolytope (Vec ℝ n)) (hXend : Bornology.IsBounded Xend.dropEqs.construct)
    (U W₀ : Zonotope (Vec ℝ n)) (Zw : ℝ → Zonotope (Vec ℝ n)) (t₀ tend : ℝ) (η ω : ℕ) :
    Set (Vec ℝ n) :=
  -- 1. Δt ← (t_end - t₀)/ω
  let Δt := (tend - t₀) / ω
  -- the box asks `ρ` about `X_end` itself, which its rows bound
  have hX : Bornology.IsBounded Xend.construct := hXend.subset Xend.construct_subset_dropEqs
  let B := Xend.zonotope (fun j => ρ Xend hX (LinearMap.proj j))    -- box(X_end)
    (fun j => ρ Xend hX (-LinearMap.proj j))
  let FB := Zonotope.mtimesIntervalMat                              -- F box(X_end), see (19)
    (MatExp.correctionMatrix (toRealMat sys.A) Δt η) B
  -- 3. μ ← √γ ‖(e^{AΔt} - I)G‖₂
  let μ := sys.maxBackReachMu Δt B
  -- 4. P₁ ← X_end ⊖ F box ⊖ B_μ
  let P₁ := LinearSys.step_maxBackReachPoly Xend FB μ
  -- 5. P₂ ← e^{AΔt}X_end ⊖ …
  let P₂ := LinearSys.step_maxBackReachPoly
    (Xend.mapEquiv (step_maxBackReach_expEquiv (toRealMat sys.A) Δt)) FB μ
  -- the two erosions keep the inequality rows bounded, `F box` and `B_μ` being nonempty
  have hμ : 0 ≤ μ := by
    letI : NormedAddCommGroup (Matrix (Fin n) (Fin B.h) ℝ) := Matrix.instL2OpNormedAddCommGroup
    exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hP : ∀ X : HPolytope (Vec ℝ n), Bornology.IsBounded X.dropEqs.construct →
      Bornology.IsBounded (LinearSys.step_maxBackReachPoly X FB μ).dropEqs.construct := fun _ h =>
    HPolytope.isBounded_dropEqs_minkDiffOf _
      (HPolytope.isBounded_dropEqs_minkDiffOf _ h ⟨FB.c, FB.center_mem_construct⟩)
      ⟨0, (Capsule.center_mem_construct_iff ⟨0, 0, μ⟩).mpr hμ⟩
  -- 2. and 6.-14. the loop over the time intervals and its union
  have hX₂ : Bornology.IsBounded                                   -- `e^{AΔt}` is Lipschitz
      (Xend.mapEquiv (step_maxBackReach_expEquiv (toRealMat sys.A) Δt)).dropEqs.construct :=
    ((LinearMap.toContinuousLinearMap (step_maxBackReach_expEquiv (toRealMat sys.A) Δt :
      Vec ℝ n →ₗ[ℝ] Vec ℝ n)).lipschitz.isBounded_image hXend).subset fun x hx =>
        ⟨_, ⟨hx.1, fun i => i.elim0⟩, LinearEquiv.apply_symm_apply _ x⟩
  sys.maxBackReachTimeInterval ρ P₁ P₂ (hP _ hXend) (hP _ hX₂) U W₀ Zw t₀ tend η ω

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
