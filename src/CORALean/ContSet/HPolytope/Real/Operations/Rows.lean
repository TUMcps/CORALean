import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.rows`

A description's own constraint normals, as the directions it is natural to
enclose an operation on. An equality row appears twice, once each way, since a
sum or a combination is bounded above and below by it.

Not a soundness matter — `ofBounds` encloses whatever directions it is given —
but the right default: the facet normals of a Minkowski sum of two polytopes are
among the two summands' own, so `plus` over this template is exact wherever the
rows are the facets.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The inequality rows, then each equality row with either sign. -/
def HPolytope.rows (P : HPolytope α) : Fin (P.m + (P.me + P.me)) → (α →ₗ[ℝ] ℝ) :=
  Fin.append P.A (Fin.append P.Ae fun i => -P.Ae i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
