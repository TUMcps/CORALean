import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
import CORALean.ContSet.Zonotope.Real.Operations.Isequal

/-!
# `ZonoBundle.isequal`

CORA's `@zonoBundle/isequal` for two bundles (`aux_isequal_zonoBundle`) at tolerance `0`: the
quick check, that the members are pairwise `isequal`, here in the sense of `Zonotope.isequal`
(same generators in the same order). CORA's second step, the mutual-containment test when the
quick check fails, is not modelled, so the test is sound but not exact. The quick check as CORA
codes it also answers `true` for bundles with different member counts: see
`ZonoBundle.isequalCora`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonoBundle/isequal` at tolerance `0`, quick check only: the same number of members, pairwise
`Zonotope.isequal`. -/
def ZonoBundle.isequal (zB S : ZonoBundle α) : Prop :=
  ∃ e : zB.k = S.k, ∀ i, (zB.Z i).isequal (S.Z (Fin.cast e i))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
