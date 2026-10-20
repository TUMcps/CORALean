module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.BoxToSlack
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows

@[expose] public section

/-!
# `HPolytope.intersection`

The constraint lists concatenate. When both error boxes are certified to be the origin
(`isErrFree`), that is all: nothing is computed, so nothing rounds, and the intersection is exact.
Otherwise a box is not a halfspace, and the intersection of two inflated descriptions has no
nominal-plus-box form. Each operand's box is paid into its own rows' slacks first (`boxToSlack`):
an inequality's slack grows by its box's support, an equality's by the larger of the box's two
supports along it, so an equality stays a slab and no right-hand side is raised (#218). The
stacked rows denote an outer approximation, with the origin box. `stackRows` is the same
concatenation without the folding.

## Inputs
* `P₁` – H-polytope
* `P₂` – H-polytope

## Output
* the stacked rows, after paying each error box into the slacks unless both are the origin
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.intersection (P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)) : HPolytope 𝕋 (Vec 𝕋 n) :=
  if P₁.isErrFree && P₂.isErrFree then P₁.stackRows P₂
  -- each box paid into its own rows' slacks, the rows as stored
  else P₁.boxToSlack.stackRows P₂.boxToSlack

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
