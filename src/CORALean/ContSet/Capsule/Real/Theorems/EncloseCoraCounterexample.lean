module

public import CORALean.ContSet.Capsule.Real.Operations.Enclose
public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# CORA's `capsule/enclose` misses the set its header documents

The header of `@capsule/enclose.m` documents `{a x₁ + (1 - a) x₂ | x₁ ∈ C, x₂ ∈ C2, a ∈ [0,1]}`
with `C2 = M*C + Cplus`, but the code sets `C2 = M*Cplus` and adds nothing. For `C = {0}`,
`M = 0` and `Cplus = {1}` the documented set contains `1` (at `a = 0`: `x₂ = M 0 + 1`), while the
code returns `{0}`. Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- The documented set `segments C (M C + Cplus)` is not inside `Capsule.enclose`. -/
theorem Capsule.enclose_cora_counterexample :
    ∃ (C Cplus : Capsule 1) (M : Mat ℝ 1 1),
      ¬ segments C.construct
          ((fun y => M.mulVec y) '' C.construct + Cplus.construct) ⊆
        (C.enclose M Cplus).construct := by -- --- PROOF ---
  refine ⟨⟨0, 0, 0⟩, ⟨fun _ => 1, 0, 0⟩, 0, fun h => ?_⟩
  have h0 : (0 : Vec ℝ 1) ∈ (Capsule.mk (0 : Vec ℝ 1) 0 0).construct :=
    ⟨0, by simp, by simp⟩
  have h1 : (fun _ => (1 : ℝ) : Vec ℝ 1) ∈
      (Capsule.mk (fun _ => (1 : ℝ) : Vec ℝ 1) 0 0).construct := ⟨0, by simp, by simp⟩
  have hm : (fun _ => (1 : ℝ) : Vec ℝ 1) ∈ segments (Capsule.mk (0 : Vec ℝ 1) 0 0).construct
      ((fun y => (0 : Mat ℝ 1 1).mulVec y) '' (Capsule.mk (0 : Vec ℝ 1) 0 0).construct +
        (Capsule.mk (fun _ => (1 : ℝ) : Vec ℝ 1) 0 0).construct) :=
    ⟨0, h0, fun _ => 1, ⟨_, ⟨0, h0, rfl⟩, fun _ => 1, h1, by simp⟩, 0, by simp, by simp⟩
  obtain ⟨t, -, ht⟩ := h hm
  simp [Capsule.enclose, Capsule.convHull, Capsule.mtimes, Capsule.radius] at ht
  norm_num at ht

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
