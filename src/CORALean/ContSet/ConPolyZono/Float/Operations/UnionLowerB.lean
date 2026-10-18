module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.unionLowerB`

Each operand's right-hand side of [1, Thm. 1], shifted by what the selector column contributes:
`b / 2`, exact, so nothing rounds and each row keeps its operand's slack.

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

/-- Each operand's right-hand side, shifted by the selector column: halved, exactly. -/
def ConPolyZono.unionLowerB {m₁ m₂ : ℕ} (b₁ : Vec 𝕋 m₁) (b₂ : Vec 𝕋 m₂) : Vec 𝕋 (m₁ + m₂) :=
  Fin.append (fun r => half (b₁ r)) (fun r => half (b₂ r))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
