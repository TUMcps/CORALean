module

public import CORALean.ContSet.Zoo.Float.Zoo
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `Zoo.ofInterval`, over a floating-point scalar

CORA's `zoo(int, N)` for coordinate `i`: the variable of the box's float zonotope, `c + r tᵢ` with
the stored centre `c` and the generator `r` (`Interval.radiusFrom`), as the Taylor model of
`Interval.taylm` and as the interval `[c - |r|, c + |r|]`, the ends rounded outward (`|r| = r` for
a nonempty box). The box lies in that interval, so it is as wide as the box or wider.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zoo.ofInterval (I : Interval (Vec 𝕋 n)) (N : ℕ) (i : Fin n) : Zoo 𝕋 n :=
  ⟨some (I.taylm N i), some ⟨fun _ => subDown (I.center i) (absolute (I.radiusFrom i)),
    fun _ => addUp (I.center i) (absolute (I.radiusFrom i))⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
