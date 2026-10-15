module

public import CORALean.ContSet.HPolytope.Real.Instances
public import CORALean.ContSet.HPolytope.Real.Operations.Eqs
public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Real.Operations.Intersection
public import CORALean.ContSet.InflatedContSet.InflatedContSet
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# Halfspace descriptions over a floating-point scalar: the representation

CORA's `polytope` with `isHRep` set, its constraint matrices held in `𝕋`, plus the error
box that makes it an `InflatedContSet`, as every other float representation has one. The
nominal part is the exact layer's polytope those stored floats describe,
`{x | A x ≤ b, Aₑ x = bₑ}`; the box holds what rounding has cost.

An inequality absorbs a rounding of its own by raising `b`. A rounded equality names a different
hyperplane; it is kept where a certified right inverse of `Aₑ` bounds the step onto the stored
hyperplane, the step paid into the box and the inequalities (`HPolytope.anchorEqs`), and is
written as the two inequalities it stands for, rounded outward, where that certificate fails.

An operation that reads the rows (a halfspace test, a dual certificate) first folds the box
into them (`HPolytope.absorbRounding`); one that moves or pads the description carries it along.

It stays at `Vec`, the only place either layer pairs a row with a point, though
`HPolytope 𝕋 α` stores its rows as a family in `α` as the exact layer does;
`HPolytope 𝕋 (Vec 𝕋 n)` is the vector case, rows of a matrix.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure HPolytope (𝕋 α : Type) where
  m : ℕ
  A : Fin m → α
  b : Vec 𝕋 m
  me : ℕ
  Ae : Fin me → α
  be : Vec 𝕋 me
  /-- The error box: everything rounding has cost so far. -/
  I_error : Interval α

/-- The exact polytope the stored floats describe, read through `toRealMat`. -/
def HPolytope.nominal [SoundFloatArithmetic 𝕋] (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    CORALean.Real.HPolytope (Vec ℝ n) :=
  (Real.HPolytope.ineqs (toRealMat P.A) (toRealVec P.b)).intersection
    (Real.HPolytope.eqs (toRealMat P.Ae) (toRealVec P.be))

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (HPolytope 𝕋 (Vec 𝕋 n)) (CORALean.Real.HPolytope (Vec ℝ n))
      (Vec 𝕋 n) (Vec ℝ n) where
  nominal := HPolytope.nominal
  I_error P := P.I_error

/-- Inherited from `InflatedContSet`: `nominal + I_error`. -/
abbrev HPolytope.construct [SoundFloatArithmetic 𝕋] (P : HPolytope 𝕋 (Vec 𝕋 n)) : Set (Vec ℝ n) :=
  InflatedContSet.construct P

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
