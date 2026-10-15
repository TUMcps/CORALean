module

public import CORALean.ContDynamics.LinParamSys.Operations.InitReachInputDependence
public import CORALean.ContDynamics.LinParamSys.Theorems.DependentHomSolOuter
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalConstCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalCorrectionMatrix
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# The corrected `initReach_inputDependence` holds the first step

`LinParamSys.initReachInputDependence_outer`: for every parameter `p ∈ [-1, 1]ᵏ` shared by the
system matrix and the constant input, every `x₀ ∈ Rinit` and every `t ∈ [0, r]`, the solution
`x(t) = e^{A(p) t} x₀ + ∫₀ᵗ e^{A(p)(t-s)} (B u(p) + c) ds`, `u(p)` in input coordinates and `B` the
center of `sys.B`, lies in the time-interval set, and `x(r)` in the time-point set
(`dependentHomSol_outer`), at the state-space constant input `B u(p) + c`.

The time-interval argument is `timeIntervalStep_outer`'s with an input: `x(t)` is the point
`(1 - t/r) x₀ + (t/r) x(r)` of `enclose(Rinit, Rhom_tp)` plus the state's curvature
`(e^{At} - I - (t/r)(e^{Ar} - I)) x₀ ∈ F Rinit` plus the input's,
`(∫₀ᵗ e^{As} ds - (t/r) ∫₀ʳ e^{As} ds) u(p) ∈ inputF Uconst`. The last is where CORA's
`inputF*center(Uconst)` falls short: `u(p)` ranges over `Uconst`, not its center.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The first step's two sets hold the solution: at the end of the step the time-point set,
at every time of it the time-interval set. -/
theorem LinParamSys.initReachInputDependence_outer (sys : LinParamSys 𝕄𝒵 n) {r : ℝ}
    (hr : 0 < r) {m : ℕ}
    (hε : ‖(Interval.smul r sys.A.interval).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (Rinit : Zonotope (Vec ℝ n)) (Uc : Vec ℝ sys.m) (UG : Fin sys.A.h → Vec ℝ sys.m)
    {p : Fin sys.A.h → ℝ} (hp : ∀ i, |p i| ≤ 1) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct Rinit)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    let A := sys.A.c + ∑ i, p i • sys.A.G i
    let u := sys.B.c *ᵥ (Uc + ∑ i, p i • UG i) + sys.c
    exp (r • A) *ᵥ x₀ + ∫ s in (0:ℝ)..r, exp ((r - s) • A) *ᵥ u
        ∈ construct (sys.initReachInputDependence r (m + 2) Rinit Uc UG).1 ∧
      exp (t • A) *ᵥ x₀ + ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u
        ∈ construct (sys.initReachInputDependence r (m + 2) Rinit Uc UG).2 := by -- --- PROOF ---
  intro A u
  -- the input in the state space, `Vc + Σ pᵢ VG i`, as `initReachInputDependence` carries it
  set Vc : Vec ℝ n := sys.B.c *ᵥ Uc + sys.c with hVc
  set VG : Fin sys.A.h → Vec ℝ n := fun i => sys.B.c *ᵥ UG i with hVG
  have hu : u = Vc + ∑ i, p i • VG i := by
    simp only [u, hVc, hVG, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul]
    abel
  have htp : exp (r • A) *ᵥ x₀ + ∫ s in (0:ℝ)..r, exp ((r - s) • A) *ᵥ u
      ∈ construct (sys.dependentHomSol r (m + 2) Rinit Vc VG) := by
    rw [hu]
    exact sys.dependentHomSol_outer hr hε Rinit Vc VG hp hx₀
  refine ⟨htp, ?_⟩
  have hAbox : A ∈ sys.A.interval.construct := Zonotope.interval_contains _ ⟨p, hp, rfl⟩
  rw [MatExp.expIntegral_constInput A u ht0]
  rw [MatExp.expIntegral_constInput A u hr.le] at htp
  -- the interpolation, the state's curvature and the input's
  have hdecomp : exp (t • A) *ᵥ x₀ + MatExp.expIntegral A t *ᵥ u
      = ((1 - t / r) • x₀ + (1 - (1 - t / r)) • (exp (r • A) *ᵥ x₀ + MatExp.expIntegral A r *ᵥ u)
          + (exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)) *ᵥ x₀)
        + (MatExp.expIntegral A t - (t / r) • MatExp.expIntegral A r) *ᵥ u := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    module
  rw [hdecomp]
  refine Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)) ?_)
  · -- `enclose(Rinit, Rhom_tp)`, at weight `1 - t/r`
    refine LinComb.linComb_outer _ _ ⟨x₀, hx₀, _, htp, 1 - t / r, ?_, rfl⟩
    exact ⟨by linarith [div_le_one_of_le₀ htr hr.le], by linarith [div_nonneg ht0 hr.le]⟩
  · -- `F Rinit`
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
      (MatExp.expDiff_mem_intervalCorrectionMatrix _ hr hε hAbox ht0 htr)
      (Set.mem_image_of_mem _ hx₀))
  · -- `inputF Uconst`: over the whole constant input (corrected)
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
      (MatExp.expIntegralDiff_mem_intervalConstCorrectionMatrix _ hr (m + 2) hε hAbox ht0 htr)
      (Set.mem_image_of_mem _ ⟨p, hp, hu⟩))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
