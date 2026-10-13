import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachTimeInterval
import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachMu
import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachPoly
import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
import CORALean.ContSet.Conversion.Real.HPolytope_to_Zonotope
import CORALean.ContSet.HPolytope.Real.Operations.MapEquiv
import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# `Alg. 2`: the maximal time-interval backward reachable set, every line

[1, Alg. 2] in full. Lines 3-5 compute the two polytopes of the inner approximated
homogeneous time-interval solution (21): `box(X_end)` from the caller's support oracle `ρ`
(the linear programs of (9)), `F box(X_end)` with `F` the interval matrix (19), `μ` (22) at
the spectral norm, `P₁ = X_end ⊖ F box(X_end) ⊖ B_μ` and `P₂ = e^{AΔt}X_end ⊖ F box(X_end) ⊖ B_μ`,
`e^{AΔt}X_end` the image of the halfspace description under the invertible `e^{AΔt}`, which is
the preimage under `e^{-AΔt}`. Lines 1-2 and 6-14 are `maxBackReachTimeInterval`, which takes
the two polytopes. Line 14's union is no constrained zonotope, so the result is a `Set`.

`Zw` is (26), the constant centre trajectory's contribution over one interval.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `e^{AΔt}` as a linear equivalence, `e^{-AΔt}` its inverse. -/
noncomputable def aux_maxBackReach_expEquiv (A : Mat ℝ n n) (Δt : ℝ) : Vec ℝ n ≃ₗ[ℝ] Vec ℝ n :=
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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: `R̂^{∃∀}(-τ)` from the target set `X_end`, lines 3-5 computed here. -/
noncomputable def LinearSys.maxBackReach (sys : LinearSys 𝕋 n)
    (ρ : ∀ (P : HPolytope (Vec ℝ n)) (c : Vec ℝ n →ₗ[ℝ] ℝ), SupportBound P.construct c)
    (Xend : HPolytope (Vec ℝ n)) (U W₀ : Zonotope (Vec ℝ n))
    (Zw : ℝ → Zonotope (Vec ℝ n)) (t₀ tend : ℝ) (η ω : ℕ) : Set (Vec ℝ n) :=
  let Δt := (tend - t₀) / ω                                         -- 1. Δt ← (t_end - t₀)/ω
  let B := Xend.zonotope (fun j => ρ Xend (LinearMap.proj j))       -- box(X_end)
    (fun j => ρ Xend (-LinearMap.proj j))
  let FB := Zonotope.mtimesIntervalMat                              -- F box(X_end), see (19)
    (MatExp.correctionMatrix (toRealMat sys.A) Δt η) B
  let μ := sys.maxBackReachMu Δt B                                  -- 3. μ ← √γ ‖(e^{AΔt} - I)G‖₂
  let P₁ := LinearSys.maxBackReachPoly Xend FB μ                    -- 4. P₁ ← X_end ⊖ F box ⊖ B_μ
  let P₂ := LinearSys.maxBackReachPoly                              -- 5. P₂ ← e^{AΔt}X_end ⊖ …
    (Xend.mapEquiv (aux_maxBackReach_expEquiv (toRealMat sys.A) Δt)) FB μ
  sys.maxBackReachTimeInterval ρ P₁ P₂ U W₀ Zw t₀ tend η ω         -- 2, 6-14

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
