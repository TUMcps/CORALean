module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.GetSubset
public import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetPoint

@[expose] public section

/-!
# `PolyLevelSet.getSubset`'s rows

The re-parametrized rows at `x` are the original ones at `x` with `xᵣ` sent to `cen + rad xᵣ`:
`PolyZonotope.getSubset_point` read at the rows' polynomial part (`lhs`), whose point at `x` is
`A μ_R(x)`.

## Inputs
* `P` – polynomial level set
* `r` – variable index
* `cen` – new center of the variable
* `rad` – new radius of the variable
* `x` – point

## Hypotheses
* none

## Conclusion
* the rows at `x` are `P`'s rows at the rescaled point
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A centerless polynomial zonotope over `Vec ℝ m`'s point is its generators, read as the columns
of a matrix, applied to the monomials. -/
theorem PolyLevelSet.aux_mulVec_eq_point {m : ℕ} (Z : PolyZonotope (Vec ℝ m)) (hc : Z.c = 0)
    (x : Fin Z.p → ℝ) :
    (fun i l => Z.G l i) *ᵥ PolyZonotope.monomial Z.E x = Z.point x := by
  funext i
  rw [PolyZonotope.point, hc, zero_add, Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_comm]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The re-parametrized rows at `x` are the original ones at `xᵣ ↦ cen + rad xᵣ`. -/
theorem PolyLevelSet.eval_getSubset (P : PolyLevelSet n) (r : Fin n) (cen rad : ℝ)
    (x : Vec ℝ n) : (P.getSubset r cen rad).eval x
      = P.eval (Function.update x r (cen + rad * x r)) := by -- --- PROOF ---
  have h : (P.getSubset r cen rad).A *ᵥ PolyZonotope.monomial (P.getSubset r cen rad).R x
      = P.A *ᵥ PolyZonotope.monomial P.R (Function.update x r (cen + rad * x r)) :=
    (PolyLevelSet.aux_mulVec_eq_point (P.lhs.getSubset r cen rad) rfl x).trans
      ((PolyZonotope.getSubset_point P.lhs r cen rad x).trans
        (PolyLevelSet.aux_mulVec_eq_point P.lhs rfl _).symm)
  exact congrArg (· - P.b) h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
