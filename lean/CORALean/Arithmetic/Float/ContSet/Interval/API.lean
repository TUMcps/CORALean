import CORALean.Arithmetic.Float.SoundFloatArithmetic
import CORALean.Arithmetic.Real.ContSet.Interval.Theorems

/-!
# Intervals over a floating-point scalar

CORA's `interval` again, with the same `inf` and `sup` fields, but held in `F`
rather than ℝ. The scalar is a parameter, so nothing here is tied to a format.

There is no second notion of what an interval denotes. `nominal` reads the
bounds through `toReal`, and `construct` is the exact layer's `construct` of
that — so a floating-point interval means the real interval its bounds describe,
by definition rather than by a lemma.

What each operation then owes is only that it encloses the exact one:
`plus_refines`, `mtimes_refines`. Soundness follows by transitivity, and the
set-level argument — Minkowski sums, images under a linear map, the sign of
`M i k` — is never repeated here.

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

def Interval.plus (I₁ I₂ : Interval F n) : Interval F n where
  inf := fun i => addDown (I₁.inf i) (I₂.inf i)
  sup := fun i => addUp (I₁.sup i) (I₂.sup i)

/-- `minimum`/`maximum` absorb the sign of `M i k` exactly as `min`/`max` do
over ℝ; the products round outward first, and the sum after. -/
def Interval.mtimes (M : Mat F m n) (I : Interval F n) : Interval F m where
  inf := fun i => sumDown fun k => minimum (mulDown (M i k) (I.inf k)) (mulDown (M i k) (I.sup k))
  sup := fun i => sumUp fun k => maximum (mulUp (M i k) (I.inf k)) (mulUp (M i k) (I.sup k))

end CORALean.Arithmetic.Float
