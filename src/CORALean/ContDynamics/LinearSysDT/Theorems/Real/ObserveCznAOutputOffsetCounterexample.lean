import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContSet.ConZonotope.Real.Operations.OfPoint
import CORALean.ContSet.ConZonotope.Real.Theorems.ConIntersectExact
import CORALean.ContSet.ConZonotope.Real.Theorems.OfPointMemIff
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

/-!
# CORA's `CZN-A` meets the measurement without the output offset `k`

`priv_observe_CZN_A` starts from `y = params.y(:,1)` (l. 44) and
`Rnext.tp = conIntersect(params.X₀, y + conZonotope(-1*params.V), linsysDT.C)` (l. 45): the
states of `R0` whose `C x` lies in `y - V`, an exact intersection with no gain. `linearSysDT`
documents `y = C x + D u + k + F v`, so the set must be `C x ∈ y - k - D u - V`. Here
`C = 1`, `k = 1`, `R0 = [-1, 1]`, `V = [-0.1, 0.1]`, `x₀ = 0`, `v₀ = 0`: the output is
`y₀ = 1`, and CORA's first set `[0.9, 1]` misses `x₀`. Every later step (l. 57-58) meets the
same strip. Read from the source, not run.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- With the output offset `k = 1`, the initial state `x₀ = 0 ∈ R0` with noise `v₀ = 0 ∈ V` is not
in `CZN-A`'s first set. -/
theorem LinearSysDT.observeCznA_output_offset_counterexample :
    let C : Mat ℝ 1 1 := 1  -- `linsysDT.C`
    let kOut : Vec ℝ 1 := fun _ => 1  -- `linsysDT.k`
    let R₀ : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ _ => 1⟩  -- `params.X₀ = [-1, 1]`
    let V : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ _ => 1 / 10⟩  -- `params.V = [-0.1, 0.1]`
    let x₀ : Vec ℝ 1 := 0
    let v₀ : Vec ℝ 1 := 0
    let y := C *ᵥ x₀ + kOut + v₀  -- `y = params.y(:,1)`, l. 44
    let Y := (ConZonotope.ofPoint y).plus (Zonotope.mtimes (-1) V).conZonotope  -- `y + ...`
    let R₁ := R₀.conZonotope.conIntersect Y C  -- `Rnext.tp = conIntersect(...)`, l. 45
    x₀ ∈ R₀.construct ∧ v₀ ∈ V.construct ∧ x₀ ∉ R₁.construct := by -- --- PROOF ---
  intro C kOut R₀ V x₀ v₀ y Y R₁
  refine ⟨⟨fun _ => 0, by simp, by funext i; simp [R₀, x₀]⟩,
    ⟨fun _ => 0, by simp, by funext i; simp [V, v₀]⟩, fun h => ?_⟩
  -- `C x₀ = y + z` with `z ∈ -V`
  rw [← ConZonotope.conIntersect_exact] at h
  obtain ⟨-, hY⟩ := h
  rw [← ConZonotope.plus_exact] at hY
  obtain ⟨a, ha, b, hb, hab⟩ := hY
  rw [ConZonotope.mem_ofPoint_iff] at ha
  rw [← Zonotope.conZonotope_exact, ← Zonotope.mtimes_exact] at hb
  obtain ⟨v, ⟨β, hβ, rfl⟩, rfl⟩ := hb
  have h0 := congrFun hab 0
  subst ha
  simp [V, y, C, x₀, kOut, v₀, Matrix.mulVec, dotProduct] at h0
  have := (abs_le.mp (hβ 0)).2
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
