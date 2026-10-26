module

public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.Definitions.SyntaxTreeFloat

@[expose] public section

/-!
# `interval(lb,ub)` over a float scalar

The one-dimensional `interval` with the bounds `lb` and `ub`, as the nodes store it, held in `𝕋`. It
rounds nothing: the interval of floats is the pair itself, so it denotes the exact `interval` of the
bounds read as reals (`SyntaxTree.contains_intervalFloat`).

## Inputs
* `lb` – lower bound
* `ub` – upper bound

## Output
* the one-dimensional interval with those bounds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `interval(lb,ub)`: the one-dimensional interval of floats with the bounds `lb` and `ub`. -/
def SyntaxTree.intervalFloat (lb ub : 𝕋) : Float.SyntaxTree.Dom 𝕋 :=
  ⟨fun _ => lb, fun _ => ub⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
