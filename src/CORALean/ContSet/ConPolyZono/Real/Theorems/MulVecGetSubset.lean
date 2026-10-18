module

public import CORALean.ContSet.ConPolyZono.Real.Operations.GetSubset
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecEqSum
public import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetPoint

@[expose] public section

/-!
# `getSubset` at the constraint columns

The expanded constraint matrix of `getSubset cPZ r cen rad` at the factor vector `a` is the
original at `a` with factor `r` sent through `αᵣ ↦ cen + rad·αᵣ`: `getSubset_point` read at the
constraint columns, each read as a polynomial zonotope with center `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `getSubset`'s constraint rows at `a` are the original's at the re-parametrized factors. -/
theorem ConPolyZono.mulVec_getSubset (cPZ : ConPolyZono α) (r : Fin cPZ.p) (cen rad : ℝ)
    (a : Fin cPZ.p → ℝ) : -- --- STMT ---
    (cPZ.getSubset r cen rad).A *ᵥ PolyZonotope.monomial (cPZ.getSubset r cen rad).R a
      = cPZ.A *ᵥ PolyZonotope.monomial cPZ.R
          (Function.update a r (cen + rad * a r)) := by -- --- PROOF ---
  -- the expanded constraint matrix at the new factors is the original at the re-parametrized
  have hL : (cPZ.getSubset r cen rad).A *ᵥ PolyZonotope.monomial (cPZ.getSubset r cen rad).R a
      = (cPZ.consPolyZonotope.getSubset r cen rad).point a := by
    unfold PolyZonotope.point
    rw [ConPolyZono.mulVec_eq_sum,
      show (cPZ.consPolyZonotope.getSubset r cen rad).c = (0 : Vec ℝ cPZ.m) from rfl, zero_add]
    exact Finset.sum_congr rfl fun x _ => rfl
  -- and the original constraint matrix at the re-parametrized factors, as a point
  have hR : cPZ.A *ᵥ PolyZonotope.monomial cPZ.R (Function.update a r (cen + rad * a r))
      = cPZ.consPolyZonotope.point (Function.update a r (cen + rad * a r)) := by
    unfold PolyZonotope.point
    rw [ConPolyZono.mulVec_eq_sum,
      show cPZ.consPolyZonotope.c = (0 : Vec ℝ cPZ.m) from rfl, zero_add]
    exact Finset.sum_congr rfl fun x _ => rfl
  -- the two agree by `getSubset_point` at the constraint columns
  exact hL.trans ((PolyZonotope.getSubset_point cPZ.consPolyZonotope r cen rad a).trans hR.symm)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
