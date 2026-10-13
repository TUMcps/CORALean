module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.mixedForm`

The bilinear form `quadMapMixed` pairs its product with itself at: `Qₖ` placed in the upper right
block of an `(n + n) × (n + n)` matrix, so that the first block of one argument is read against the
second block of the other, and on an appended pair `(x₁, x₂)` it is `x₁ᵀ Qₖ x₂`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Qₖ` placed to read the first block of a pair against the second: `(x₁, x₂) ↦ (y₁, y₂) ↦
x₁ᵀ Qₖ y₂`. -/
def PolyZonotope.mixedForm (Q : Fin m → Mat 𝕋 n n) : Fin m → Mat 𝕋 (n + n) (n + n) :=
  fun k r r' =>
    Fin.addCases (motive := fun _ => 𝕋)
      (fun a => Fin.addCases (motive := fun _ => 𝕋) (fun _ => zero) (fun b => Q k a b) r')
      (fun _ => zero) r

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
