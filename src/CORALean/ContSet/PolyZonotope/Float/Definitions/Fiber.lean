module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# The points of a polynomial zonotope at one value of its factors

A polynomial zonotope's points are a function of its dependent factors `a` and its independent
ones `β`. `fiber` is the set of points at `a`: the dependent part (center plus generators times
monomials) with an independent part and a point of the error box added to it. Two sets that share
factors (`exactPlus`) agree on the points at one `a`; the set is the union of its fibers over the
unit box (`mem_toSet_iff_fiber`).

## Inputs
* `pZ` – polynomial zonotope
* `a` – value of the dependent factors

## Output
* the set of points at `a`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The points of `pZ` at the factor values `a`: the center plus the generators times their
monomials, an independent part in the unit box, and a point of the error box. -/
def PolyZonotope.fiber [SoundFloatArithmetic 𝕋] (pZ : PolyZonotope (Vec 𝕋 n))
    (a : Fin pZ.p → ℝ) : Set (Vec ℝ n) :=
  {x | ∃ β : Fin pZ.q → ℝ, (∀ j, |β j| ≤ 1) ∧ ∃ e ∈ pZ.I_error.toSet,
    x = (fun i => toReal (pZ.c i) + ∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l)
      + (fun i => ∑ j, toReal (pZ.GI j i) * β j) + e}

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
