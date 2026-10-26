module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosureFloat
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.Specification.STL.Operations.DepReachStepFloat
public import CORALean.Specification.STL.Theorems.DepBoxFloatOuter

@[expose] public section

/-!
# One float pass of the loop encloses the real pass

The loop pass of [1, Alg. 1] is a matrix exponential `e^{AΔt}` that lies in the float
`expIntervalEnclosure` of `Δt A` (`exp_mem_expIntervalEnclosure`, `smul_outer`), so
`mtimesIntervalMat_outer` holds its image of each set the float state holds. `T ũ` and `T U₀` are
images by a member of `T` in the same way, the sums are `plus_outer` and `D_{i+1}` is
`depBoxFloat_outer`. The set `E` standing for `C_i` is mapped by `e^{AΔt}` the same way.
## Inputs
* `A` – float dynamics matrix
* `Δt` – float time step
* `η` – Taylor order of the matrix exponential
* `csR` – real constants
* `csF` – float constants
* `sR` – real state
* `sF` – float state
* `E` – exact set standing for `C_i`

## Hypotheses
* `hε` – the float norm bound is small enough for the Taylor order
* `hcs` – the float constants enclose the real ones
* `h` – the float state encloses the real one

## Conclusion
* the float state one step later encloses the real one, with `E` mapped by `e^{AΔt}`
## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise Matrix NormedSpace Float Float.FloatOps Float.SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The float pass from `t_i` to `t_{i+1}` encloses the real pass of an enclosed state. -/
theorem STL.depReachStepFloat_outer (A : Mat 𝕋 n n) (Δt : 𝕋) {η : ℕ}
    (hε : toReal (MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point A))) /
      ((η : ℝ) + 2) ≤ 1 / 2) {csR : STL.DepReachConsts n} {csF : STL.DepReachConstsFloat 𝕋 n}
    {sR : STL.DepReachState n} {sF : STL.DepReachStateFloat 𝕋 n} {E : Set (Vec ℝ n)}
    (hcs : csF.Encloses csR) (h : sF.Encloses sR E) : -- --- CONCL ---
    (STL.depReachStepFloat A Δt η csF sF).Encloses
      (STL.depReachStep (toRealMat A) (toReal Δt) csR sR)
      ((exp (toReal Δt • toRealMat A) *ᵥ ·) '' E) := by -- --- PROOF ---
  obtain ⟨hu, hU₀, hT, -, -, hD⟩ := hcs
  set Φ := exp (toReal Δt • toRealMat A)
  -- the real exponential lies in the float enclosure of the point box `Δt A`
  have hΦ : Φ ∈
      (MatExp.expIntervalEnclosure (Interval.smul Δt Δt (Interval.point A)) η).construct :=
    MatExp.exp_mem_expIntervalEnclosure _ η
      (Interval.smul_outer le_rfl le_rfl _ (Float.Interval.mem_point A)) hε
  -- the image by a member of an interval matrix lies in the float product
  have key : ∀ {M : Mat ℝ n n} {IM : Interval (Mat 𝕋 n n)} {S : Set (Vec ℝ n)}
      {Z : Float.Zonotope (Vec 𝕋 n)}, M ∈ IM.construct → S ⊆ Z.construct →
      (M *ᵥ ·) '' S ⊆ (Float.Zonotope.mtimesIntervalMat IM Z).construct := by
    rintro M IM S Z hM hS _ ⟨x, hx, rfl⟩
    exact Float.Zonotope.mtimesIntervalMat_outer _ _ (Set.mem_iUnion₂.2 ⟨M, hM, ⟨x, hS hx, rfl⟩⟩)
  have hTu : csR.T *ᵥ csR.ũ ∈ (Float.Zonotope.mtimesIntervalMat csF.T csF.ũ).construct :=
    key hT (Set.singleton_subset_iff.2 hu) ⟨csR.ũ, rfl, rfl⟩
  have hTU : (Real.Zonotope.mtimes csR.T csR.U₀).construct ⊆
      (Float.Zonotope.mtimesIntervalMat csF.T csF.U₀).construct := by
    rw [← Real.Zonotope.mtimes_exact]
    exact key hT hU₀
  -- the four sets, then the box of `D`
  unfold STL.depReachStepFloat STL.depReachStep
  dsimp only
  refine ⟨?_, ?_, ?_, key hΦ h.2.2.2⟩
  · rw [← Real.Zonotope.plus_exact, ← Real.Zonotope.mtimes_exact]
    refine (Set.add_subset_add (key hΦ h.1) ?_).trans (Float.Zonotope.plus_outer _ _)
    intro x hx
    rw [Real.Zonotope.mem_ofPoint_iff] at hx
    rw [hx]
    exact hTu
  · rw [← Real.Zonotope.plus_exact, ← Real.Zonotope.mtimes_exact]
    exact (Set.add_subset_add (key hΦ h.2.1) hTU).trans (Float.Zonotope.plus_outer _ _)
  · refine STL.depBoxFloat_outer ?_
    rw [← Real.Zonotope.plus_exact, ← Real.Zonotope.mtimes_exact]
    exact (Set.add_subset_add (key hΦ h.2.2.1) hD).trans (Float.Zonotope.plus_outer _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
