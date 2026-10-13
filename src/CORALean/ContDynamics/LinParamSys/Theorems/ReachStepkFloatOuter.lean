import CORALean.ContDynamics.LinParamSys.Operations.ReachStepkFloat
import CORALean.ContDynamics.LinParamSys.Theorems.ExpMemExpSquaringFloat
import CORALean.ContDynamics.LinParamSys.Theorems.SquaringsFloatSpec
import CORALean.ContDynamics.LinearSys.Theorems.SampleTimeFloatMem

/-!
# A window `reachStepkFloat` returns holds every member's flow from the first

`e^{A t_k}` is in the window's matrix at every member `A`: `t_k` is in its bracket
(`sampleTimeFloat_mem`), the squaring count is admissible (`squaringsFloat_spec`),
and `exp_mem_expSquaringFloat` encloses the rest.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.reachStepkFloat_outer
    (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n) {Δt : 𝕋} {η k : ℕ}
    (h2 : 2 ≤ η) {Rτ₀ R : Zonotope (Vec 𝕋 n)} (h : sys.reachStepkFloat Δt η Rτ₀ k = some R)
    {A : Mat ℝ n n} (hA : A ∈ sys.A.construct) {y : Vec ℝ n} (hy : y ∈ Rτ₀.construct) :
    exp (((k : ℝ) * toReal Δt) • A) *ᵥ y ∈ R.construct := by -- --- PROOF ---
  simp only [LinParamSys.reachStepkFloat, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨sk, hsk, rfl⟩ := h
  -- `t_k` lies in its bracket
  obtain ⟨hLo, hHi⟩ := LinearSys.sampleTimeFloat_mem Δt k
  exact Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (S := fun k => Zonotope (Vec 𝕋 k)) _ Rτ₀
    (Set.mem_biUnion (sys.exp_mem_expSquaringFloat (LinParamSys.squaringsFloat_spec h2 hsk) hA
      hLo hHi) (Set.mem_image_of_mem _ hy))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
