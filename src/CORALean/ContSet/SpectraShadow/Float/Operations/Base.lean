import CORALean.ContSet.Interval.Float.Operations.Origin
import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

/-!
# `SpectraShadow.base`, over a floating-point scalar

CORA's `spectraShadow(SpS.A)`: the base spectrahedron, the variables `β` themselves as the
points, centre `0`, identity generators and the origin box. The stored matrices are the shadow's
own, so nothing rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


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
  E := Interval.origin S.m

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
