module

public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# An interval inside another

`J` lies inside `I` when its bounds do; every `intPrev & ...` of `syntaxTree.m` yields such a `J`.

## Inputs
* `J` – inner interval
* `I` – outer interval

## Output
* the inner interval lies inside the outer one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `J` lies inside `I`: `I`'s bounds enclose `J`'s. -/
def SyntaxTree.Dom.within (J I : Dom) : Prop := I.inf 0 ≤ J.inf 0 ∧ J.sup 0 ≤ I.sup 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
