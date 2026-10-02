import CORALean.ContSet.Interval.Float.Operations.Times
import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# `Interval.prod₁` over floats

CORA's `@interval/prod` of an interval matrix along dimension 1 at a floating-point scalar: the
rows are multiplied together entrywise with the float `times`, which rounds each bound outward, so
the stored box holds every column product the exact one does. The fold starts at the point `1`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows multiplied together by `times`, the last row first. -/
def Interval.prod₁ (I : Interval (Mat 𝕋 m n)) : Interval (Vec 𝕋 n) :=
  -- row `i` of the interval matrix, `I(i, :)`
  let row : Fin m → Interval (Vec 𝕋 n) := fun i => ⟨fun j => I.inf i j, fun j => I.sup i j⟩
  Fin.foldr m (fun i res => (row i).times res) (Interval.point (fun _ => (one : 𝕋)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
