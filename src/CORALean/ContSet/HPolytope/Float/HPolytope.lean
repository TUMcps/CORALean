module

public import CORALean.ContSet.HPolytope.Real.Operations.Slab
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# Halfspace descriptions over a floating-point scalar: the representation

CORA's `polytope` with `isHRep` set, its constraint matrices held in `𝕋`, and one
difference from the exact layer: the equality right-hand side is an `Interval`.

That is where rounding goes. An inequality absorbs its own by raising `b`, the
way an interval absorbs it into its bounds. An equality cannot — any rounding of
`Ae` or `be` names a different hyperplane, and a hyperplane has empty interior,
so the rounded set and the exact one generally meet in less than either. An
ambient error box does not rescue it either: the box is added after the
constraints have chosen a point, and a rounded equality system can be infeasible
where the exact one is not. The slack has to sit on the constraint, so `be` is an
interval and the row reads `Ae x ∈ be`.

The nominal reading is the exact layer's `slab`, so every operation owes only enclosure.
It stays at `Vec`, the only place either layer pairs a row with a point, though
`HPolytope 𝕋 α` stores its rows as a family in `α` as the exact layer does;
`HPolytope 𝕋 (Vec 𝕋 n)` is the vector case, rows of a matrix.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
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
  /-- Interval-valued, unlike the exact layer's point: this is where an
  equality's rounding goes. -/
  be : Interval (Vec 𝕋 me)

def HPolytope.nominal [SoundFloatArithmetic 𝕋] (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    CORALean.Real.HPolytope (Vec ℝ n) :=
  (Real.HPolytope.ineqs (toRealMat P.A) (toRealVec P.b)).intersection
    (Real.HPolytope.slab (toRealMat P.Ae) (toRealVec P.be.inf) (toRealVec P.be.sup))

/-- The set a polytope of stored floats stands for: its nominal's. Without an error box there is
nothing to inflate, so this is the class's `construct`, spelt for `P.construct` to resolve. -/
def HPolytope.construct [SoundFloatArithmetic 𝕋] (P : HPolytope 𝕋 (Vec 𝕋 n)) : Set (Vec ℝ n) :=
  P.nominal.construct

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
