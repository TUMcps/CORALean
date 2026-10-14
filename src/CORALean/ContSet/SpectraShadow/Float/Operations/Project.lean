module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.project` over a floating-point scalar

The centre and every generator read at the chosen coordinates, the inequality untouched, and
the error box projected with `Interval.project`. Selecting coordinates moves stored floats
without arithmetic, so nothing rounds. `dims` may repeat or reorder coordinates.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.project (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (dims : Fin m → Fin n) : SpectraShadow
    𝕋 (Vec 𝕋 m) where
  k := S.k
  m := S.m
  A₀ := S.A₀
  A := S.A
  c := fun i => S.c (dims i)
  G := fun j i => S.G j (dims i)
  I_error := S.I_error.project dims

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
