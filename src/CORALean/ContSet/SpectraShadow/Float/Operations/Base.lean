module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.base`, over a floating-point scalar

CORA's `spectraShadow(SpS.A)`: the base spectrahedron, the variables `β` themselves as the
points, center `0`, identity generators and the origin box. The stored matrices are the shadow's
own, so nothing rounds.

## Inputs
* `S` – spectrahedral shadow

## Output
* the base spectrahedron, with `β` as points, center `0` and identity generators
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.base (S : SpectraShadow 𝕋 (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 S.m) where
  k := S.k
  m := S.m
  A₀ := S.A₀
  A := S.A
  c := fun _ => zero
  G := fun j r => if r = j then one else zero
  I_error := Interval.origin S.m

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
