module

public import CORALean.ContSet.Interval.Float.Operations.Origin
public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.singletonOne`, over a floating-point scalar

`spectraShadow([1 0 -1 0; 0 -1 0 1])`: `diag(1 - β, β - 1) ⪰ 0`, the point `{1}` of `ℝ¹`, from
`one`, `zero` and the exact negation of `one`. The box is the origin.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

abbrev SpectraShadow.singletonOne : SpectraShadow 𝕋 (Vec 𝕋 1) where
  k := 2
  m := 1
  A₀ := fun p q => if p = q then (if p = 0 then one else neg one) else zero
  A := fun _ p q => if p = q then (if p = 0 then neg one else one) else zero
  c := fun _ => zero
  G := fun _ _ => one
  E := Interval.origin 1

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
