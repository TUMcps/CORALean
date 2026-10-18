module

public import CORALean.ContSet.ConPolyZono.Real.Operations.PlusA
public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.unionLowerA`

The lower half of [1, Thm. 1]'s constraint matrix, its `A_L`: the two operands'
own constraint systems side by side, plus one shared column read against `α₁`,
which is what makes each system bind on its own branch and fall away on the other.

[1] puts `∓0.5 b` in that column; the shift lands in `unionLowerB`.

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

/-- Both operands' systems, plus the selector column that switches them. -/
noncomputable def ConPolyZono.unionLowerA {m₁ q₁ m₂ q₂ : ℕ} (A₁ : Mat ℝ m₁ q₁)
    (b₁ : Vec ℝ m₁) (A₂ : Mat ℝ m₂ q₂) (b₂ : Vec ℝ m₂) :
    Mat ℝ (m₁ + m₂) (q₁ + q₂ + 1) :=
  fun i => Fin.append (ConPolyZono.plusA A₁ A₂ i)
    (fun _ => Fin.append (fun r => -(2⁻¹ * b₁ r)) (fun r => 2⁻¹ * b₂ r) i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
