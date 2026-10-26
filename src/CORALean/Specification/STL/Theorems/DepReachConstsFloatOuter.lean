module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AdaptiveIntegralOuterRefines
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegralSubSumMemAdaptiveRemainder
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.Specification.STL.Operations.DepReachConstsOfFloat
public import CORALean.Specification.STL.Theorems.DepBloatingFloatOuter
public import CORALean.Specification.STL.Theorems.DepCurvatureFFloatOuter
public import CORALean.Specification.STL.Theorems.DepCurvatureGFloatOuter

@[expose] public section

/-!
# Line 1 over floats encloses the real constants

The constants of line 1 of [1, Alg. 1] computed in floats hold the real ones: `ũ = B c_u` is a
point of the float product of `B` with the point `c_u`; `U₀ = B(U ⊕ (-c_u))` is the image of a sum
of sets, held by the float sum and product (`plus_outer`, `mtimes_outer`); `T` is in the float
integrated exponential (`adaptiveIntegral_outer_refines`) as the integral of the exponential is in
the exact one; `F`, `G` and `D` are `depCurvatureFFloat_outer`, `depCurvatureGFloat_outer` and
`depBloatingFloat_outer`.

## Inputs
* `A` – float dynamics matrix
* `B` – float input matrix
* `Δt` – float time step
* `κ` – Taylor order
* `Ur` – real input zonotope
* `Uf` – float input zonotope

## Hypotheses
* `hr` – the time step is nonnegative
* `hε` – the float norm bound is small enough for the Taylor order
* `hc` – the real input zonotope has the center of the float one
* `hU` – the real input zonotope lies inside the float one

## Conclusion
* the float constants hold the real constants
## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float constants hold the real ones of a real input zonotope inside the float one. -/
theorem STL.depReachConstsFloat_outer (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) {Δt : 𝕋}
    (hr : 0 ≤ toReal Δt) (κ : ℕ)
    (hε : toReal (MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point A))) /
      ((κ : ℝ) + 2) ≤ 1 / 2) {Ur : Real.Zonotope (Vec ℝ m)} {Uf : Float.Zonotope (Vec 𝕋 m)}
    (hc : Ur.c = toRealVec Uf.c) (hU : Ur.construct ⊆ Uf.construct) : -- --- CONCL ---
    (STL.depReachConstsFloat A B Uf Δt κ).Encloses
      (STL.depReachConsts (toRealMat A) (toRealMat B) Ur (toReal Δt) κ) := by -- --- PROOF ---
  have hM : toRealMat A ∈ (Interval.point A).construct := Float.Interval.mem_point A
  -- the centered input set `U ⊕ (-c_u)`, mapped by `B`, is held by the float one
  have hU₀ : (Real.Zonotope.mtimes (toRealMat B)
      (Ur.plus (Real.Zonotope.ofPoint (-Ur.c)))).construct
      ⊆ (Float.Zonotope.mtimes B (Uf.plus (Float.Zonotope.point (-Uf.c)))).construct := by
    rw [← Real.Zonotope.mtimes_exact, ← Real.Zonotope.plus_exact]
    rintro _ ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩
    rw [Real.Zonotope.mem_ofPoint_iff] at hv
    refine Float.Zonotope.mtimes_outer B _ ⟨u + v, Float.Zonotope.plus_outer _ _
      (Set.add_mem_add (hU hu) ?_), rfl⟩
    rw [Float.Zonotope.construct_point, Set.mem_singleton_iff, hv, hc, toRealVec_neg]
  unfold STL.DepReachConstsFloat.Encloses STL.depReachConsts STL.depReachConstsFloat
  dsimp only
  refine ⟨?_, hU₀, ?_, STL.depCurvatureFFloat_outer A hr κ hε,
    STL.depCurvatureGFloat_outer A hr κ hε, STL.depBloatingFloat_outer A hr κ hε hU₀⟩
  · -- `ũ = B c_u` is held by the float product with the point `c_u`
    refine Float.Zonotope.mtimes_outer B _ ⟨toRealVec Uf.c, ?_, by rw [hc]⟩
    rw [Float.Zonotope.construct_point]; rfl
  · -- the integral of the exponential is in the float integrated exponential
    have hint : Real.MatExp.expIntegral (toRealMat A) (toReal Δt) ∈
        (Real.MatExp.adaptiveIntegral (toRealMat A) (toReal Δt) κ).construct := by
      refine Real.Interval.mem_mat_iff.mpr fun j k => ?_
      have hmem := Real.Interval.mem_mat_iff.mp
        (Real.MatExp.expIntegral_sub_sum_mem_adaptiveRemainder (toRealMat A) hr κ) j k
      simp only [Real.MatExp.adaptiveIntegral, Real.MatExp.adaptiveRemainder,
        Matrix.sub_apply] at hmem ⊢
      constructor <;> linarith [hmem.1, hmem.2]
    exact MatExp.adaptiveIntegral_outer_refines (Interval.point A) hr κ hε hM hint

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
