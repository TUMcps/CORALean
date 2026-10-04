import CORALean.ContSet.ZonoBundle.Real.Operations.IsequalCora

/-!
# CORA's `zonoBundle/isequal` quick check accepts bundles of different sets

The bundle `{[-1, 1]}` of one member against `{[-1, 1], {2}}` of two: the first denotes
`[-1, 1]`, the second `[-1, 1] ∩ {2} = ∅`, yet the member counts differ, so the quick check
returns `true` (`ZonoBundle.isequalCora`). Read from the source, not run.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The quick check holds for two bundles that denote different sets. -/
theorem ZonoBundle.isequal_cora_counterexample :
    ∃ zB S : ZonoBundle (Vec ℝ 1), zB.isequalCora S ∧
      zB.construct ≠ S.construct := by -- --- PROOF ---
  -- the interval `[-1, 1]` and the point `2`
  let Z : Zonotope (Vec ℝ 1) := ⟨1, fun _ => 0, fun _ _ => 1⟩
  let W : Zonotope (Vec ℝ 1) := ⟨0, fun _ => 2, fun j => j.elim0⟩
  refine ⟨⟨1, fun _ => Z⟩, ⟨2, fun i => if i = 0 then Z else W⟩, Or.inl (by simp), ?_⟩
  intro h
  -- the origin is in the first and not in the second
  have h0 : (0 : Vec ℝ 1) ∈ (ZonoBundle.mk 1 fun _ => Z).construct := by
    refine Set.mem_iInter.mpr fun _ => ⟨fun _ => 0, fun _ => by simp, ?_⟩
    funext i
    simp [Z]
  rw [h] at h0
  have hW := Set.mem_iInter.mp h0 1
  obtain ⟨β, -, hβ⟩ := hW
  have := congrFun hβ 0
  simp [W] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
