import CORALean.ContSet.Interval.Float.Operations.Origin
import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

/-!
# `SpectraShadow.hyperplaneOne`, over a floating-point scalar

The hyperplane `ℝⁿ × {1}` of `ℝⁿ⁺¹` of `convHull_`: the trivial inequality `0 ⪰ 0`, the centre `(0,
1)` and the unit vectors of the first `n` coordinates as generators. The box is the origin.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps


-- =====================================  MAIN DEFINITION  ====================================== --

abbrev SpectraShadow.hyperplaneOne (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) : SpectraShadow
    𝕋 (Vec 𝕋 (n + 1)) where
  k := 1
  m := n
  A₀ := fun _ _ => zero
  A := fun _ _ _ => zero
  c := Fin.append (fun _ => zero) (fun _ : Fin 1 => one)
  G := fun j r => Fin.append (fun i : Fin n => if i = j then one else zero)
    (fun _ : Fin 1 => zero) r
  E := Interval.origin (n + 1)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
