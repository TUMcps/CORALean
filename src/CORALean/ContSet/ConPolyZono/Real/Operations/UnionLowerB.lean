module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.unionLowerB`

What the operands' rows are held to once `unionLowerA`'s selector column has
shifted them: each operand's own right-hand side, moved down by `0.5 b` to `0.5 b`, which is
what [1, Thm. 1] writes. On the operand's own branch the shift cancels and the row is the
operand's constraint unchanged; on the other branch the row reads `0.5 b` and holds.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Each operand's right-hand side, shifted by what the selector column contributes. -/
noncomputable def ConPolyZono.unionLowerB {m₁ m₂ : ℕ} (b₁ : Vec ℝ m₁) (b₂ : Vec ℝ m₂) :
    Vec ℝ (m₁ + m₂) :=
  Fin.append (fun r => 2⁻¹ * b₁ r) (fun r => 2⁻¹ * b₂ r)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
