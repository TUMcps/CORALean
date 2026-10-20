module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.ReindexVars
public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.compactFactors`

The factors neither block reads, dropped. Only `p` and the two exponent
matrices change; every generator, every constraint column and `b` stand. The constraint is its
own `PolyLevelSet.reindexVars` at the used factors.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Output
* same set with unused factors dropped
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The factors neither block reads, dropped. Only `p` and the two exponent
matrices change; every generator, every constraint column and `b` stand. -/
def ConPolyZono.compactFactors (cPZ : ConPolyZono α) : ConPolyZono α where
  p := (ConPolyZono.usedFactors cPZ.E cPZ.cons.R).card
  h := cPZ.h
  qI := cPZ.qI
  c := cPZ.c
  G := cPZ.G
  E := fun k i => cPZ.E (ConPolyZono.factorIdx cPZ.E cPZ.cons.R k) i
  GI := cPZ.GI
  cons := cPZ.cons.reindexVars (ConPolyZono.factorIdx cPZ.E cPZ.cons.R)
  cons_eq := cPZ.cons_eq
  cons_dom := by
    show cPZ.cons.dom.project _ = _
    rw [cPZ.cons_dom]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
