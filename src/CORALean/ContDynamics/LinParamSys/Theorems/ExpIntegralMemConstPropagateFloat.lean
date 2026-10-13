import CORALean.ContDynamics.LinParamSys.Operations.ConstPropagateFloat
import CORALean.ContDynamics.LinParamSys.Theorems.ExpIntegralMemConstInputSolutionFloat
import CORALean.ContDynamics.LinParamSys.Theorems.ExpMemExpIntervalFloat
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec

/-!
# `constPropagateFloat` holds what a constant input contributes by each window start

What the constant `ũ` contributes by `t_k = k Δt` at a member `A` of `sys.A`, `∫₀^{t_k} e^{Aσ}dσ ũ`,
is carried across one more window by `expIntegral_add_mulVec`: `e^{AΔt}` of its value at `t_k`
plus its value over `Δt`, the first in `[e^{[A]Δt}] P̃(t_k)`, the second in `P̃^R(τ_0)`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix ContSet NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- What the constant `ũ` contributes by `t_k = k Δt`, at any member `A` of `sys.A`, lies in
`constPropagateFloat Δt η ρ ũ k`, at an order admissible for `Δt`. -/
theorem LinParamSys.expIntegral_mem_constPropagateFloat
    (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n) {Δt : 𝕋} {η : ℕ} (ρ : ℕ)
    (hΔt : 0 < toReal Δt) (hη : sys.OrderAdmissibleFloat Δt Δt η) {A : Mat ℝ n n}
    (hA : A ∈ sys.A.construct) (uc : Vec 𝕋 n) (k : ℕ) :
    Real.MatExp.expIntegral A ((k : ℝ) * toReal Δt) *ᵥ Scalar.toRealVec uc
      ∈ (sys.constPropagateFloat Δt η ρ uc k).construct := by -- --- PROOF ---
  induction k with
  | zero =>
    -- nothing has been contributed by `t_0 = 0`, and `{0}` holds that
    have hz : Real.MatExp.expIntegral A (((0 : ℕ) : ℝ) * toReal Δt) = 0 := by
      simp [Real.MatExp.expIntegral]
    rw [hz, Matrix.zero_mulVec]
    have h0 := OfScalarPoint.mem_ofVec (S := fun k => Zonotope (Vec 𝕋 k))
      (fun _ : Fin n => (zero : 𝕋))
    rwa [show Scalar.toRealVec (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
  | succ k ih =>
    -- the value by `t_{k+1}` comes apart at `Δt`
    have hrec := Real.MatExp.expIntegral_add_mulVec A (Scalar.toRealVec uc)
      (a := (k : ℝ) * toReal Δt) (b := toReal Δt) (by positivity) hΔt.le
    have htk : ((k + 1 : ℕ) : ℝ) * toReal Δt = (k : ℝ) * toReal Δt + toReal Δt := by
      push_cast; ring
    rw [htk, hrec]
    -- the earlier part, carried across one window by `[e^{[A]Δt}]`
    have h1 : exp (toReal Δt • A) *ᵥ (Real.MatExp.expIntegral A ((k : ℝ) * toReal Δt)
        *ᵥ Scalar.toRealVec uc) ∈ construct (Mtimes.mtimes (S := fun k => Zonotope (Vec 𝕋 k))
          (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (sys.expIntervalFloat Δt Δt η)
          (sys.constPropagateFloat Δt η ρ uc k)) :=
      Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n))
        (S := fun k => Zonotope (Vec 𝕋 k)) _ _
        (Set.mem_biUnion (sys.exp_mem_expIntervalFloat hη hA (le_refl _) (le_refl _))
          (Set.mem_image_of_mem _ ih))
    -- the new window's part
    have h2 := sys.expIntegral_mem_constInputSolutionFloat hΔt hη hA uc hΔt.le le_rfl
    exact Reduce.reduce_outer _ ρ (Plus.plus_outer _ _ (Set.add_mem_add h1 h2))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
