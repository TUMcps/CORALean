import CORALean.ContSet.HPolytope.Real.Operations.Slab
import CORALean.ContSet.Interval.Float.Interval

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

The nominal reading is the exact layer's `slab`, so what this denotes is fixed by
definition rather than by a lemma, and every operation owes only enclosure.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

structure HPolytope (𝕋 : Type) (n : ℕ) where
  m : ℕ
  A : Mat 𝕋 m n
  b : Vec 𝕋 m
  me : ℕ
  Ae : Mat 𝕋 me n
  /-- Interval-valued, unlike the exact layer's point: this is where an
  equality's rounding goes. -/
  be : Interval 𝕋 me

def HPolytope.nominal [SoundFloatArithmetic 𝕋] (P : HPolytope 𝕋 n) :
    CORALean.Real.HPolytope (Vec ℝ n) :=
  (Real.HPolytope.ineqs (toRealMat P.A) (toRealVec P.b)).and
    (Real.HPolytope.slab (toRealMat P.Ae) (toRealVec P.be.inf) (toRealVec P.be.sup))

def HPolytope.construct [SoundFloatArithmetic 𝕋] (P : HPolytope 𝕋 n) : Set (Vec ℝ n) :=
  P.nominal.construct

/-- Membership in this polytope's own fields, which is the form every operation
below states its obligation in. -/
theorem HPolytope.mem_construct_iff [SoundFloatArithmetic 𝕋] {P : HPolytope 𝕋 n}
    {x : Vec ℝ n} :
    x ∈ P.construct ↔
      (∀ i, (toRealMat P.A *ᵥ x) i ≤ toReal (P.b i))
        ∧ ∀ i, toReal (P.be.inf i) ≤ (toRealMat P.Ae *ᵥ x) i
               ∧ (toRealMat P.Ae *ᵥ x) i ≤ toReal (P.be.sup i) := by
  have hand : x ∈ P.construct ↔
      x ∈ (Real.HPolytope.ineqs (toRealMat P.A) (toRealVec P.b)).construct
        ∧ x ∈ (Real.HPolytope.slab (toRealMat P.Ae) (toRealVec P.be.inf)
            (toRealVec P.be.sup)).construct := Real.HPolytope.mem_and_iff
  rw [hand, Real.HPolytope.mem_ineqs_iff, Real.HPolytope.mem_slab_iff]
  exact Iff.rfl

end CORALean.Float
