module

public import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA

@[expose] public section

/-!
# `ConPolyZono.unionLowerA`

The operands' own constraint systems side by side, plus the shared selector column
of [1, Thm. 1]: `∓ b / 2`. Halving and negation are exact, so nothing here
rounds, and the matrix reads back as the exact layer's (`toRealMat_unionLowerA`).

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both operands' systems, plus the selector column that switches them. -/
def ConPolyZono.unionLowerA {m₁ q₁ m₂ q₂ : ℕ} (A₁ : Mat 𝕋 m₁ q₁)
    (b₁ : Vec 𝕋 m₁) (A₂ : Mat 𝕋 m₂ q₂) (b₂ : Vec 𝕋 m₂) :
    Mat 𝕋 (m₁ + m₂) (q₁ + q₂ + 1) :=
  fun i => Fin.append (ConPolyZono.plusA A₁ A₂ i)
    (fun _ => Fin.append (fun r => neg (half (b₁ r))) (fun r => half (b₂ r)) i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
