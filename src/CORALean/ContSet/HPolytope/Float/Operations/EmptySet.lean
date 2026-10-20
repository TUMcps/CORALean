module

public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `HPolytope.emptySet`, over a floating-point scalar

The single constraint `0 ≤ -1`, which no point satisfies, as over ℝ. `neg one` is
exact, so reading it back gives `-1` and nothing is rounded.

## Inputs
* `𝕋` – scalar type
* `n` – natural number

## Output
* the polytope with the single row `0 ≤ -1`, which no point satisfies
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.emptySet (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) : HPolytope 𝕋 (Vec 𝕋 n) where
  m := 1
  A := fun _ _ => zero
  b := fun _ => neg one
  me := 0
  Ae := fun i => i.elim0
  be := fun i => i.elim0
  b_error := fun _ => zero
  be_error := fun _ => zero
  I_error := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
