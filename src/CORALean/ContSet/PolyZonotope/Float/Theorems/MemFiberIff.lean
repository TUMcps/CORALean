module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.NominalPointEq
public import CORALean.ContSet.PolyZonotope.Float.Definitions.Fiber

@[expose] public section

/-!
# A fiber point, with its dependent part named

`fiber` unfolds to the dependent part at `a` plus an independent part and a point of the error
box; this restates it with the nominal point `pZ.nominal.point a` in place of the inlined sum.

## Inputs
* `pZ` – polynomial zonotope
* `a` – factor values
* `x` – point

## Hypotheses
* none

## Conclusion
* `x` is in the fiber iff it is the nominal point plus an independent part plus an error point
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of a fiber, read with the nominal point named. -/
theorem PolyZonotope.mem_fiber_iff (pZ : PolyZonotope (Vec 𝕋 n)) (a : Fin pZ.p → ℝ)
    (x : Vec ℝ n) : -- --- CONCL ---
    x ∈ pZ.fiber a ↔ ∃ β : Fin pZ.q → ℝ, (∀ j, |β j| ≤ 1) ∧ ∃ e ∈ pZ.I_error.toSet,
      x = pZ.nominal.point a + (fun i => ∑ j, toReal (pZ.GI j i) * β j) + e := by -- --- PROOF ---
  have hp : pZ.nominal.point a = fun i => toReal (pZ.c i)
      + ∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l :=
    PolyZonotope.nominal_point_eq pZ a
  rw [hp]
  exact Iff.rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
