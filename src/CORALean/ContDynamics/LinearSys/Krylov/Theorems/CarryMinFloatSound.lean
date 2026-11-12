module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.CarryMinFloat
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# The smaller of two sound carries is sound

If `e ≤ g` and `e ≤ w` for the two carried bounds of [1, Sec. 7], then
`e ≤ Krylov.carryMinFloat g w`: whatever error is bounded by both is bounded by the smaller. The
error `e` is any real quantity, at any time of a window, so this holds of every bound of
`Krylov.windowErrorBoundFloat` and of the Gershgorin carry alike.

## Inputs
* `g` – the Gershgorin carry
* `w` – the Lyapunov-weighted carry
* `e` – the error

## Hypotheses
* `hg` – the error is within `g`
* `hw` – the error is within `w`

## Conclusion
* the error is within the smaller of the two

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

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `e ≤ g` and `e ≤ w` give `e ≤ min(g, w)`. -/
theorem Krylov.carryMinFloat_sound (g w : 𝕋) (e : ℝ) (hg : e ≤ toReal g) (hw : e ≤ toReal w) :
    e ≤ toReal (Krylov.carryMinFloat g w) := by
  rw [Krylov.carryMinFloat, toReal_minimum]
  exact le_min hg hw

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
