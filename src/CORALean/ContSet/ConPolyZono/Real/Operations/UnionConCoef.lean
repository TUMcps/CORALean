module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# `ConPolyZono.unionConCoef`

The one constraint row of [1, Thm. 1]'s selector constraint, column by column,
against the monomials `unionConCol` names. The normalizations `1/(2p)` and
`1/(4p₁p₂)` are what turn the bare square sums into the means `unionMeanSq`
reads, which is what keeps the row's value inside a range the proof can use.

Where an operand has no factors the corresponding group is empty, so the
division by a zero count is never evaluated at a column that exists.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The coefficients of the selector constraint's single row. -/
noncomputable def ConPolyZono.unionConCoef (p₁ p₂ : ℕ) :
    Fin (2 + (p₁ + p₁ + (p₂ + p₂ + (p₁ * p₂ + p₁ * p₂)))) → ℝ :=
  Fin.append ![1, -1]
    (Fin.append
      (Fin.append (fun _ => (2 * (p₁ : ℝ))⁻¹) (fun _ => -(2 * (p₁ : ℝ))⁻¹))
      (Fin.append
        (Fin.append (fun _ => -(2 * (p₂ : ℝ))⁻¹) (fun _ => -(2 * (p₂ : ℝ))⁻¹))
        (Fin.append (fun _ => -(4 * ((p₁ : ℝ) * (p₂ : ℝ)))⁻¹)
          (fun _ => (4 * ((p₁ : ℝ) * (p₂ : ℝ)))⁻¹))))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
