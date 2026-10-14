module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Logic.Function.CompTypeclasses

@[expose] public section

/-!
# A polynomial zonotope as a zonotope — the construction

`PolyZonotope.zonotope`, `PolyZonotope.evenWeight` and `PolyZonotope.zonotopeEven` are the
constructions; `PolyZonotope_to_Zonotope` states and proves what they guarantee.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   13-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.zonotope (pZ : PolyZonotope α) : Zonotope α where
  h := pZ.h + pZ.q
  c := pZ.c
  G := Fin.append pZ.G pZ.GI

/-- How much of a dependent generator is left free: none of a constant column,
half of an all-even one, all of the rest. -/
noncomputable def PolyZonotope.evenWeight {p h : ℕ} (E : Fin p → Fin h → ℕ) (i : Fin h) : ℝ :=
  if ∀ k, E k i = 0 then 0 else if ∀ k, E k i % 2 = 0 then 1 / 2 else 1

/-- The paper's `N`, `H` and `K` read off column by column rather than as three
index sets: a zero weight is a generator the paper drops. -/
noncomputable def PolyZonotope.zonotopeEven (pZ : PolyZonotope α) : Zonotope α where
  h := pZ.h + pZ.q
  c := pZ.c + ∑ i, (1 - PolyZonotope.evenWeight pZ.E i) • pZ.G i
  G := Fin.append (fun i => PolyZonotope.evenWeight pZ.E i • pZ.G i) pZ.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
