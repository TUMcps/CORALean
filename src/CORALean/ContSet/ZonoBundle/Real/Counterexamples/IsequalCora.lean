module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Isequal

@[expose] public section

/-!
# The quick check of CORA's `zonoBundle/isequal`, as coded

`aux_isequal_zonoBundle` starts with `res = true;` and clears it only inside
`if zB.parallelSets == S.parallelSets`, in the loop over the members. With different member counts
the loop never runs, `res` stays `true`, and `if res return end` answers `true` without the
containment test that follows. Read from the source, not run. With the same count and a member
that differs the quick check clears `res` and falls through to the containment test, whose answer
is not modelled; so the quick check returns `true` exactly when the counts differ or all members
agree.

# CORA's `zonoBundle/isequal` quick check accepts bundles of different sets

The bundle `{[-1, 1]}` of one member against `{[-1, 1], {2}}` of two: the first denotes
`[-1, 1]`, the second `[-1, 1] ∩ {2} = ∅`, yet the member counts differ, so the quick check
returns `true` (`ZonoBundle.isequalCora`). Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- The model: CORA's code as printed, kept only to be refuted.
/-- When the quick check of `aux_isequal_zonoBundle` returns `true` (before any containment test):
the member counts differ, or they agree and every member is `isequal`. -/
def ZonoBundle.isequalCora (zB S : ZonoBundle α) : Prop :=
  zB.k ≠ S.k ∨ zB.isequal S

end CORALean.Real

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
