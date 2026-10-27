module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDrift
public import CORALean.Global.Partition

@[expose] public section

/-!
# `PolyZonotope.relaxDrift`

`eDrift` at the pair a partition names, read as an interval's midpoint and half-width rather
than its two ends. That is the form a relaxation consumes: the midpoint is a constant the
center absorbs and the half-width is what the new independent generator carries, so a drift of
`[-ξ_E, 0]` costs half of what `[-ξ_E, ξ_E]` does. Both are halves of a natural number, hence
exact in the float layer: `[1, Thm. 1]` scales one generator by a count read off the exponent
matrix, and halving a stored float rounds nothing.

## Inputs
* `pZ` – polynomial zonotope
* `part` – split with two selected generators
* `k₀` – factor index

## Output
* pair of center-shift amounts of the relaxation

## References

* [1] [T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its Applications
      in Formal Neural Network Verification". Proceedings of the AAAI Conference on Artificial
      Intelligence, 2024.](../../../../../../references/2024/ladner-aaai-exponent-relaxation.md)
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The drift interval's midpoint and half-width, in copies of the relaxed
generator, from the `[-lo, hi]` that `eDrift` reads off the exponents. -/
noncomputable def PolyZonotope.relaxDrift (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : ℝ × ℝ :=
  ((((PolyZonotope.eDrift pZ.E k₀ (part.right 0) (part.right 1)).2 : ℝ)
      - ((PolyZonotope.eDrift pZ.E k₀ (part.right 0) (part.right 1)).1 : ℝ)) / 2,
    (((PolyZonotope.eDrift pZ.E k₀ (part.right 0) (part.right 1)).2 : ℝ)
      + ((PolyZonotope.eDrift pZ.E k₀ (part.right 0) (part.right 1)).1 : ℝ)) / 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
