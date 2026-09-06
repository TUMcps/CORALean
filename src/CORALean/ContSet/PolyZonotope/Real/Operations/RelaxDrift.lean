import CORALean.ContSet.PolyZonotope.Real.Operations.EDrift
import CORALean.Global.Partition

/-!
# `PolyZonotope.relaxDrift`

`eDrift` at the pair a partition names, read as an interval's midpoint and
half-width rather than as its two ends. That is the form a relaxation consumes:
the midpoint is a constant the centre absorbs and the half-width is what the new
independent generator has to carry, so a drift of `[-ξ_E, 0]` costs half of what
the symmetric `[-ξ_E, ξ_E]` does.

Both are multiples of the relaxed generator, and both are halves of a natural
number, which is why they are exact in the float layer too: `[1, Thm. 1]` scales
one generator by a count read off the exponent matrix, and halving a stored
float rounds nothing.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The drift interval's midpoint and half-width, in copies of the relaxed
generator, from the `[-lo, hi]` that `eDrift` reads off the exponents. -/
noncomputable def PolyZonotope.relaxDrift (PZ : PolyZonotope α)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : ℝ × ℝ :=
  ((((PolyZonotope.eDrift PZ.E k₀ (part.right 0) (part.right 1)).2 : ℝ)
      - ((PolyZonotope.eDrift PZ.E k₀ (part.right 0) (part.right 1)).1 : ℝ)) / 2,
    (((PolyZonotope.eDrift PZ.E k₀ (part.right 0) (part.right 1)).2 : ℝ)
      + ((PolyZonotope.eDrift PZ.E k₀ (part.right 0) (part.right 1)).1 : ℝ)) / 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
