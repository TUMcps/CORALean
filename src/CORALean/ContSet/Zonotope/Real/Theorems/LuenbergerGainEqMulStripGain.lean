module

public import CORALean.ContSet.Zonotope.Real.Operations.LuenbergerGain
public import CORALean.ContSet.Zonotope.Real.Operations.StripGain

@[expose] public section

/-!
# The two observers' gains differ by the state matrix

[1, Eq. 35]: `Λᵥ = F Λₛ`, the set-propagation gain (Eq. 31) the strip-based gain (Eq. 38)
multiplied by `F` on the left, for the same zonotope, measurement matrix and measurement noise.
"It can be easily shown": the two formulas differ in the leading `F` only.

## Inputs
* `F` – dynamics matrix
* `Γ` – stacked measurement matrix
* `R` – measurement-noise generators
* `X` – zonotope

## Hypotheses
* none

## Conclusion
* the Luenberger gain is `F` times the strip gain

## References

* [1] [A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      2023.](../../../../../../references/2023/alanwar-jfi-diffusion-observers.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p nr : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.luenbergerGain_eq_mul_stripGain (F : Mat ℝ n n) (Γ : Mat ℝ p n)
    (R : Mat ℝ p nr) (X : Zonotope (Vec ℝ n)) :
    Zonotope.luenbergerGain F Γ R X = F * Zonotope.stripGain Γ R X := by
  -- both are products of the same factors, `F` associated to the left
  simp only [Zonotope.luenbergerGain, Zonotope.stripGain, Matrix.mul_assoc]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
