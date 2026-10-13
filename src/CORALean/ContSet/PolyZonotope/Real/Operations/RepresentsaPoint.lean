module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.representsa_point`

CORA's `@polyZonotope/representsa_` at type `point`: after `compact_(pZ,'all',eps)` no dependent and
no independent generator is left. Here the sufficient test without the compaction: every
generator is `0`. CORA's compaction also merges generators with equal exponent columns and
drops the ones that cancel, so it answers `true` for more sets than this does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `polyZonotope/representsa_` at `point`, before compaction: every generator vanishes. -/
def PolyZonotope.representsa_point (pZ : PolyZonotope α) : Prop :=
  (∀ i, pZ.G i = 0) ∧ ∀ j, pZ.GI j = 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
