import CORALean.Arithmetic.Float.SoundFloatArithmetic
import CORALean.Arithmetic.Real.ContSet.Interval.Theorems

/-!
# Intervals over a floating-point scalar

CORA's `interval` with the same `inf` and `sup`, held in `F` rather than ℝ.

`nominal` reads the bounds through `toReal` and `construct` is the exact layer's
`construct` of that, so what an interval denotes is fixed by definition, not by
a lemma. Each operation then owes only that it encloses the exact one; soundness
follows by transitivity, and no set-level argument is repeated here.

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

variable {F : Type} [FloatOps F] {n m : ℕ}

structure Interval (F : Type) (n : ℕ) where
  inf : Vec F n
  sup : Vec F n

def Interval.nominal [SoundFloatArithmetic F] (I : Interval F n) :
    CORALean.Arithmetic.Real.Interval n :=
  ⟨toRealVec I.inf, toRealVec I.sup⟩

def Interval.construct [SoundFloatArithmetic F] (I : Interval F n) : Set (Vec ℝ n) :=
  I.nominal.construct

instance [SoundFloatArithmetic F] : Real.ContSet (Interval F n) n := ⟨Interval.construct⟩

/-! ## Boxes built from rounding data

Neither mentions a representation; the generator counterpart does, and lives
with `Zonotope`. -/

/-- The intended vector is in `[lo, hi]` but `stored` was written down. -/
def Interval.residual (lo hi stored : Vec F n) : Interval F n :=
  ⟨fun i => subDown (lo i) (stored i), fun i => subUp (hi i) (stored i)⟩

/-- The box `[-r, r]`. -/
def Interval.symmetric (r : Vec F n) : Interval F n := ⟨fun i => neg (r i), r⟩

def Interval.plus (I₁ I₂ : Interval F n) : Interval F n where
  inf := fun i => addDown (I₁.inf i) (I₂.inf i)
  sup := fun i => addUp (I₁.sup i) (I₂.sup i)

/-- `minimum`/`maximum` absorb the sign of `M i k` as `min`/`max` do over ℝ. -/
def Interval.mtimes (M : Mat F m n) (I : Interval F n) : Interval F m where
  inf := fun i => sumDown fun k => minimum (mulDown (M i k) (I.inf k)) (mulDown (M i k) (I.sup k))
  sup := fun i => sumUp fun k => maximum (mulUp (M i k) (I.inf k)) (mulUp (M i k) (I.sup k))

end CORALean.Arithmetic.Float
