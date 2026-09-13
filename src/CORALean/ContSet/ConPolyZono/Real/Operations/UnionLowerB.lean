import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.unionLowerB`

What the operands' rows are held to once `unionLowerA`'s selector column has
shifted them: each operand's own bounds, moved down by `0.5 b.inf`. On the
operand's own branch the shift cancels and the row is the operand's constraint
unchanged; on the other branch the row reads `0.5 b.inf`, which lies in the
shifted bounds exactly when `b.inf ≤ b.sup`.

Where [1]'s `b` is crisp both ends are `0.5 b`, which is what [1, Thm. 1] writes.

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

/-- Each operand's bounds, shifted by what the selector column contributes. -/
noncomputable def ConPolyZono.unionLowerB {m₁ m₂ : ℕ} (b₁ : Interval (Vec ℝ m₁))
    (b₂ : Interval (Vec ℝ m₂)) : Interval (Vec ℝ (m₁ + m₂)) :=
  ⟨Fin.append (fun r => 2⁻¹ * b₁.inf r) (fun r => 2⁻¹ * b₂.inf r),
    Fin.append (fun r => b₁.sup r - 2⁻¹ * b₁.inf r) (fun r => b₂.sup r - 2⁻¹ * b₂.inf r)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
