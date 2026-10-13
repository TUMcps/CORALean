import CORALean.ContSet.ZonoBundle.Real.Operations.Isequal

/-!
# The quick check of CORA's `zonoBundle/isequal`, as coded

`aux_isequal_zonoBundle` starts with `res = true;` and clears it only inside
`if zB.parallelSets == S.parallelSets`, in the loop over the members. With different member counts
the loop never runs, `res` stays `true`, and `if res return end` answers `true` without the
containment test that follows. Read from the source, not run. With the same count and a member
that differs the quick check clears `res` and falls through to the containment test, whose answer
is not modelled; so the quick check returns `true` exactly when the counts differ or all members
agree.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- When the quick check of `aux_isequal_zonoBundle` returns `true` (before any containment test):
the member counts differ, or they agree and every member is `isequal`. -/
def ZonoBundle.isequalCora (zB S : ZonoBundle α) : Prop :=
  zB.k ≠ S.k ∨ zB.isequal S

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
