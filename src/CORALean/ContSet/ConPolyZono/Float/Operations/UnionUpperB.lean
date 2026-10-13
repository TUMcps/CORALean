module

public import CORALean.ContSet.ConPolyZono.Float.Operations.PlusB
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConErr

@[expose] public section

/-!
# `ConPolyZono.unionUpperB`

What the two selector rows of [1, Thm. 1] are held to: `α₁α₂ = 1` exactly, and the scaled selector
polynomial within `unionConErr` of `0`, the rounding of its integer coefficients paid
into the bound.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The right-hand sides of the two selector rows. -/
def ConPolyZono.unionUpperB (p₁ p₂ : ℕ) : Interval (Vec 𝕋 (1 + 1)) :=
  ConPolyZono.plusB ⟨fun _ => one, fun _ => one⟩
    ⟨fun _ : Fin 1 => neg (ConPolyZono.unionConErr p₁ p₂ : 𝕋),
      fun _ : Fin 1 => (ConPolyZono.unionConErr p₁ p₂ : 𝕋)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
