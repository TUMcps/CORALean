module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.unionLowerB`

Each operand's bounds of [1, Thm. 1], shifted by what the selector column contributes: the lower end
is `b.inf / 2`, exact, and the upper end `b.sup - b.inf / 2` rounded up, so the
interval only ever widens.

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

/-- Each operand's bounds, shifted by the selector column and rounded outward. -/
def ConPolyZono.unionLowerB {m₁ m₂ : ℕ} (b₁ : Interval (Vec 𝕋 m₁))
    (b₂ : Interval (Vec 𝕋 m₂)) : Interval (Vec 𝕋 (m₁ + m₂)) :=
  ⟨Fin.append (fun r => half (b₁.inf r)) (fun r => half (b₂.inf r)),
    Fin.append (fun r => subUp (b₁.sup r) (half (b₁.inf r)))
      (fun r => subUp (b₂.sup r) (half (b₂.inf r)))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
