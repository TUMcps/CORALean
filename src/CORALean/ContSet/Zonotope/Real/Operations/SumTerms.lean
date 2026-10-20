module

public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

/-!
# A Minkowski sum of zonotopes, term by term

`E_err = 0; for i = ...; E_err = E_err + term_i; end` of CORA's loops: the Minkowski sum of
`f 0, …, f (m - 1)`, from the point `0`, one `plus` at a time, as [1]'s loops do.

## Inputs
* `f` – indexed family of zonotopes

## Output
* Minkowski sum of the first terms

## References

* [1] `contDynamics/@linearSys/trajectoryError.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `f 0 ⊕ … ⊕ f (m - 1)`, `{0}` for `m = 0`. -/
def Zonotope.sumTerms (f : ℕ → Zonotope α) : ℕ → Zonotope α
  | 0 => Zonotope.ofPoint 0
  | m + 1 => (Zonotope.sumTerms f m).plus (f m)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
