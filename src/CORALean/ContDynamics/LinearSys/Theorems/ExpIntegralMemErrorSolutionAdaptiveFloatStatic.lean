module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AdaptiveIntegralOuterRefines
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegralSubSumMemAdaptiveRemainder
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemErrorSolutionAdaptiveFloat

@[expose] public section

/-!
# `errorSolutionAdaptiveFloat` with a static input

A dynamic point `v` and a static point `s` held over the step contribute
`∫₀^Δt e^{Aσ}dσ (v + s)`. The dynamic part is the case without a static set; the static part
is `∫₀^Δt e^{Aσ}dσ` times `s`, and that matrix is in the exact `eAtInt`
(`expIntegral_sub_sum_mem_adaptiveRemainder`), so in the float one
(`adaptiveIntegral_outer_refines`). Outer only, held inputs only, by [1, Lemma 1].

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order
* `Vdyn` – dynamic noise float zonotope
* `Vstat` – static noise float zonotope
* `v` – dynamic input value
* `s` – static input value

## Hypotheses
* `hΔt` – step length positive
* `hη` – order admissible
* `hv` – dynamic value lies in its zonotope
* `hs` – static value lies in its zonotope

## Conclusion
* what the two held inputs contribute lies in the float error solution with the static input

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- At `Δt > 0` and an order the float enclosures admit, `∫₀^Δt e^{Aσ}dσ (v + s)` is in the
float error solution for every `v ∈ Vdyn` and `s ∈ Vstat`. -/
theorem LinearSys.expIntegral_mem_errorSolutionAdaptiveFloat_static (sys : LinearSys 𝕋 n)
    {Δt : 𝕋} {η : ℕ} (hΔt : 0 < toReal Δt) (hη : sys.IsOrderAdmissibleFloat Δt Δt η)
    {Vdyn Vstat : Zonotope (Vec 𝕋 n)} {v s : Vec ℝ n} (hv : v ∈ Vdyn.construct)
    (hs : s ∈ Vstat.construct) : -- --- CONCL ---
    Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal Δt) *ᵥ v
        + Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal Δt) *ᵥ s
      ∈ (sys.errorSolutionAdaptiveFloat Δt η Vdyn (some Vstat)).construct := by -- --- PROOF ---
  set A := Scalar.toRealMat sys.A with hA
  have hdyn := sys.expIntegral_mem_errorSolutionAdaptiveFloat hΔt hη hv
  -- the integrated exponential is in the exact `eAtInt`, so in the float one
  have hint : Real.MatExp.expIntegral A (toReal Δt)
      ∈ (Real.MatExp.adaptiveIntegral A (toReal Δt) η).construct := by
    refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
    have hmem := Real.Interval.mem_mat_iff.mp
      (Real.MatExp.expIntegral_sub_sum_mem_adaptiveRemainder A hΔt.le η) j k
    simp only [Real.MatExp.adaptiveIntegral, Real.MatExp.adaptiveRemainder,
      Matrix.sub_apply] at hmem ⊢
    constructor <;> linarith [hmem.1, hmem.2]
  have hintF := MatExp.adaptiveIntegral_outer_refines (Interval.point sys.A) hΔt.le η hη.2
    (Interval.mem_point sys.A) hint
  have hstat := Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
    (S := 𝒵[𝕋])
    (MatExp.adaptiveIntegral (Interval.point sys.A) Δt η) Vstat
    (Set.mem_biUnion hintF (Set.mem_image_of_mem _ hs))
  exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hdyn hstat)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
