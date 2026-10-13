import CORALean.ContDynamics.LinearSys.MatExp.Operations.CurvatureEnclosureFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalConstCorrectionMatrixFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrectionMatrixFloat
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Interval.Float.Theorems.MemPoint

/-!
# The float curvature enclosure holds the true deviation from the straight line

`C = F H(t_k) ⊕ G ũ` encloses, for every matrix `M` the box `A` holds, every point `x` of
`H(t_k)` and every time `τ ∈ [0, Δt]`, the deviation of the affine flow
`e^{τM}x + ∫₀^τ e^{Mσ}dσ ũ` from the straight line between its values at `0` and `Δt`:
`(e^{τM} - I - (τ/Δt)(e^{ΔtM} - I)) x + (∫₀^τ - (τ/Δt)∫₀^Δt) ũ`. This is the object
`Real.MatExp.curvatureEnclosure` encloses. `intervalCorrectionMatrix` holds the first factor
and `intervalConstCorrectionMatrix` the second, each at the members of `A`, and `mtimes_outer`
and `plus_outer` carry them through the products.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.curvatureEnclosure_outer (A : Interval (Mat 𝕋 n n)) {H : Zonotope (Vec 𝕋 n)}
    {ũ : Vec 𝕋 n} {Δt : 𝕋} {η : ℕ} (hΔt : 0 < toReal Δt) (hη : 2 ≤ η)
    (hε : toReal (MatExp.normUpperBound (Interval.smul Δt Δt A)) / ((η : ℝ) + 2) ≤ 1 / 2)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) {x : Vec ℝ n} (hx : x ∈ H.construct) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ toReal Δt) :
    (exp (τ • M) - 1 - (τ / toReal Δt) • (exp (toReal Δt • M) - 1)) *ᵥ x
      + (Real.MatExp.expIntegral M τ
          - (τ / toReal Δt) • Real.MatExp.expIntegral M (toReal Δt)) *ᵥ toRealVec ũ
      ∈ (MatExp.curvatureEnclosure A H ũ Δt η).construct := by -- --- PROOF ---
  obtain ⟨m, rfl⟩ : ∃ m, η = m + 2 := ⟨η - 2, by omega⟩
  have hF := MatExp.expDiff_mem_intervalCorrectionMatrix A hΔt (by exact_mod_cast hε) hM hτ0 hτ
  have hG := MatExp.expIntegralDiff_mem_intervalConstCorrectionMatrix A hΔt (m + 2) hε hM hτ0 hτ
  have hpt : toRealVec ũ ∈ (Interval.point ũ).zonotope.construct :=
    Interval.zonotope_contains _ (Interval.mem_point ũ)
  exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add
    (Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n))
      (S := fun k => Zonotope (Vec 𝕋 k)) _ H
      (Set.mem_biUnion hF (Set.mem_image_of_mem _ hx)))
    (Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k)) _
      (Interval.point ũ).zonotope
      (Set.mem_biUnion hG (Set.mem_image_of_mem _ hpt))))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
