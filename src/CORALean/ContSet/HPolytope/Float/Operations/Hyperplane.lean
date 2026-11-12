module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic

@[expose] public section

/-!
# `HPolytope.hyperplane?`

The normal `n` and offset `γ` of a halfspace description that is exactly one hyperplane
`n·x = γ`: no inequality row, one equality row, no slack and no error box. This is the guard
shape `Location.guardIntersectZonoGirardFloat` takes. Any other description gives `none`,
including a hyperplane with inequalities (CORA tightens the box by them).

## Inputs
* `P` – halfspace description

## Output
* the normal and the offset, none if `P` is not a bare hyperplane
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(a, d)` if `P` denotes exactly `{x | a·x = d}`: one equality row, no inequality rows,
`isErrFree`. -/
def HPolytope.hyperplane? (P : HPolytope 𝕋 (Vec 𝕋 n)) : Option (Vec 𝕋 n × 𝕋) :=
  if h : P.isErrFree = true ∧ P.m = 0 ∧ P.me = 1 then
    some (P.Ae ⟨0, by omega⟩, P.be ⟨0, by omega⟩)
  else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
