import CORALean.Arithmetic.Float.ContSet.Interval.Structure

/-!
# Intervals over a floating-point scalar: the operations

Each bound rounds away from the interval: `inf` down, `sup` up. That is the
whole of the floating-point content.

Guarantees live in `Theorems`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}

/-! ## Boxes built from rounding data

Neither mentions a representation; the generator counterpart does, and lives
with `Zonotope`. -/

/-- The intended vector is in `[lo, hi]` but `stored` was written down. -/
def Interval.residual (lo hi stored : Vec 𝕋 n) : Interval 𝕋 n :=
  ⟨fun i => subDown (lo i) (stored i), fun i => subUp (hi i) (stored i)⟩

/-- The box `[-r, r]`. -/
def Interval.symmetric (r : Vec 𝕋 n) : Interval 𝕋 n := ⟨fun i => neg (r i), r⟩

def Interval.plus (I₁ I₂ : Interval 𝕋 n) : Interval 𝕋 n where
  inf := fun i => addDown (I₁.inf i) (I₂.inf i)
  sup := fun i => addUp (I₁.sup i) (I₂.sup i)

/-- `minimum`/`maximum` absorb the sign of `M i k` as `min`/`max` do over ℝ. -/
def Interval.mtimes (M : Mat 𝕋 m n) (I : Interval 𝕋 n) : Interval 𝕋 m where
  inf := fun i => sumDown fun k => minimum (mulDown (M i k) (I.inf k)) (mulDown (M i k) (I.sup k))
  sup := fun i => sumUp fun k => maximum (mulUp (M i k) (I.inf k)) (mulUp (M i k) (I.sup k))

end CORALean.Arithmetic.Float
