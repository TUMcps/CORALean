module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyRAOuterVerdictCora

@[expose] public section

/-!
# CORA's `reachavoid:zonotope` verifies a set touching the unsafe set

`d_Fo <= 0` (`priv_verifyRA_zonotope.m` l. 280) accepts `d_Fo = 0`, which is what
`aux_distanceIntersectionZono` returns when the outer approximation meets the unsafe set in a
single point. For `ẋ = 0` from `X₀ = [-1, 1]` (the reachable set is `X₀`, so `Z = [-1, 1]`) and the
unsafe set `x ≥ 1`, the reachable state `1` is unsafe, yet the verdict is `true`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The verdict is `true` although `1 ∈ Z` lies in the unsafe set `x ≥ 1`. -/
theorem LinearSys.verifyRAOuterVerdictCora_touch_counterexample :
    LinearSys.verifyRAOuterVerdictCora (Set.Icc (-1) 1) (Set.Ici 1) = true ∧
      (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 ∩ Set.Ici 1 := by -- --- PROOF ---
  have hS : Set.Icc (-1 : ℝ) 1 ∩ Set.Ici 1 = {1} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact le_antisymm h h'
    · rintro rfl; norm_num
  refine ⟨?_, by rw [hS]; rfl⟩
  have hne : (Set.Icc (-1 : ℝ) 1 ∩ Set.Ici 1).Nonempty := ⟨1, by rw [hS]; rfl⟩
  have hd : LinearSys.verifyRAIntersectionDistanceCora (Set.Icc (-1 : ℝ) 1 ∩ Set.Ici 1) = 0 := by
    rw [hS]; simp [LinearSys.verifyRAIntersectionDistanceCora]
  simp [LinearSys.verifyRAOuterVerdictCora, hne, hd]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
