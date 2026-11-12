module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# The smaller of two carried errors, in floats

[1, Sec. 7] carries the error of earlier restart windows into the next one in more than one way:
by the growth `e^{tμ_A}` of the Gershgorin bound (`Krylov.restarted_error_le`) and, for a stable
non-normal matrix, in a Lyapunov weight (`Krylov.windowErrorBoundFloat`). Both are bounds of the
same error, so the smaller one is reported; the smaller of two upper bounds is an upper bound
(`Krylov.carryMinFloat_sound`). This is the choice of CORA.cpp's `KrylovWindows`.

## Inputs
* `g` – the Gershgorin carry
* `w` – the Lyapunov-weighted carry

## Output
* the smaller of the two bounds

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `min(g, w)`. -/
def Krylov.carryMinFloat (g w : 𝕋) : 𝕋 :=
  minimum g w

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
