module

public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Interval.dirac`, over a floating-point scalar

CORA's `@interval/dirac`: an enclosure of the `n`-th derivative of the Dirac delta over the box.
Where the strict tests `ltStrict` certify that the box misses `0` the result is exactly `0`;
elsewhere the delta's value at `0` is unbounded and that end is left open. At `n = 0` the lower
bound is `0` throughout (`δ ≥ 0`); at `n ≥ 1` both ends are open where `0` is not excluded. Not as
sharp as CORA's sign case analysis, which closes one side when `0` is an endpoint: `le` only
certifies a `true` answer, so an endpoint `0` is not told from a box straddling it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.dirac (n : ℕ) (I : Interval (Vec 𝕋 m)) : Interval.EBox 𝕋 m :=
  let miss : Fin m → Bool := fun i => ltStrict zero (I.inf i) || ltStrict (I.sup i) zero
  ⟨fun i => if n = 0 ∨ miss i = true then some zero else none,
    fun i => if miss i = true then some zero else none⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
