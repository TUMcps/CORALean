import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `ConPolyZono.unionMeanSq`

The mean of the squares of a block of factors, which is what [1, Thm. 1]'s
selector constraint measures each operand's block by: it is `0` exactly when
every factor of the block is, and it stays in `[0,1]` over the unit cube, which
is what makes the second branch of the constraint solvable only at `0`.

At `p = 0` the sum is empty and `(0 : ℝ)⁻¹` is `0`, so this is `0` — the value the
degenerate block should have, and the reason no positivity hypothesis is needed.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `p⁻¹ ∑ aₖ²`, the normalized square sum of one factor block. -/
noncomputable def ConPolyZono.unionMeanSq {p : ℕ} (a : Fin p → ℝ) : ℝ :=
  (p : ℝ)⁻¹ * ∑ k, a k ^ 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
