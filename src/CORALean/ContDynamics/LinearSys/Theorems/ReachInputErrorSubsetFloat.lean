module

public import CORALean.ContDynamics.LinearSys.Operations.ReachInputError
public import CORALean.ContDynamics.LinearSys.Operations.ReachInputErrorFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepErrorBoxSubsetFloat
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# The float input error holds the exact one

`reachInputErrorFloat` encloses `reachInputError` at every step count, by induction on it. A
step carries the previous error through `e^{AΔt}`, which `[e^{AΔt}]` holds
(`exp_mem_expIntervalFloat`) and `mtimes_outer` carries over the set, and adds the box paid at
that step, which `timePointStepErrorBox_subset_float` holds. The exact layer's operations are
exact (`mtimes_exact`, `plus_exact`), so only the float side loses ground.

An enclosure is the direction an inner approximation needs of what it takes off.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic InflatedContSet NormedSpace
open scoped Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachInputError_subset_float (sys : LinearSys 𝕋 n) {Δt : 𝕋}
    (hΔt : 0 ≤ toReal Δt) {η : ℕ} (hη : sys.OrderAdmissibleFloat Δt Δt η)
    (U : Zonotope (Vec 𝕋 n)) (k : ℕ) :
    (sys.reachInputError (toReal Δt) η (nominal U) k).construct ⊆
      ContSet.construct (sys.reachInputErrorFloat Δt η U k) := by -- --- PROOF ---
  have heA := sys.exp_mem_expIntervalFloat hη (t := toReal Δt) le_rfl le_rfl
  have hbox := sys.timePointStepErrorBox_subset_float hΔt hη U
  induction k with
  | zero =>
    -- both accumulators start at the origin
    rintro x ⟨β, -, rfl⟩
    have h0 : (sys.reachInputError (toReal Δt) η (nominal U) 0).c
        + ∑ j, β j • (sys.reachInputError (toReal Δt) η (nominal U) 0).G j = 0 := by
      simp [LinearSys.reachInputError, Real.Zonotope.ofPoint]
    rw [h0]
    show (0 : Vec ℝ n) ∈ (Zonotope.point fun _ : Fin n => (zero : 𝕋)).construct
    rw [Zonotope.construct_point]
    funext i
    simp [toRealVec, toReal_zero]
  | succ k ih =>
    -- one step: the previous error through `e^{AΔt}`, and the box paid afresh
    intro x hx
    have hx' : x ∈ (Real.Zonotope.mtimes (sys.discretize (toReal Δt)).A
        (sys.reachInputError (toReal Δt) η (nominal U) k)).construct
          + (sys.timePointStepErrorBox (toReal Δt) η (nominal U)).construct := by
      rw [Real.Zonotope.plus_exact]
      exact hx
    obtain ⟨y, hy, b, hb, rfl⟩ := hx'
    rw [← Real.Zonotope.mtimes_exact] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact Plus.plus_outer _ _ (Set.add_mem_add
      (Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n)) _ _
        (Set.mem_biUnion heA (Set.mem_image_of_mem _ (ih hz)))) (hbox hb))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
