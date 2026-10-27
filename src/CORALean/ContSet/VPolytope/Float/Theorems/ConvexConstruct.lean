module

public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.VPolytope.Real.Theorems.Convex
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# A float vertex description is convex

What a float vertex description denotes is a nominal hull plus an error box, so `Convex.add`
carries convexity across: the hull is convex as over ℝ, the box because its coordinates are
bounded independently. It holds at any ambient type the exact layer's `Entrywise` covers, so at
`Mat 𝕋 m n` too.

## Inputs
* `P` – vertex description

## Hypotheses
* none

## Conclusion
* the denoted set is convex
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] [Entrywise β ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.convex_construct (P : VPolytope α) : Convex ℝ (InflatedContSet.construct P) :=
  Convex.add P.nominal.convex_construct P.I_error.nominal.convex_construct

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
