module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# The set spanned by a list of generators

`LinearSys.verifyZonoGenSet G = {Σⱼ βⱼ gⱼ | |βⱼ| ≤ 1}`, by recursion on the list: the empty list
spans `{0}`, and `g :: G` the points `β g + y` with `|β| ≤ 1` and `y` spanned by `G`. Appending
lists adds the sets, which is how the zonotope verification adds generators step by step.

## Inputs
* `q` – dimension
* `G` – generators

## Output
* the set of their combinations with coefficients in `[-1, 1]`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `{Σⱼ βⱼ gⱼ | |βⱼ| ≤ 1}` for the generators `G`. -/
def LinearSys.verifyZonoGenSet {q : ℕ} (G : List (Vec ℝ q)) : Set (Vec ℝ q) :=
  match G with
  | [] => {0}
  | g :: G => {x | ∃ β : ℝ, |β| ≤ 1 ∧ ∃ y ∈ LinearSys.verifyZonoGenSet G, x = β • g + y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
