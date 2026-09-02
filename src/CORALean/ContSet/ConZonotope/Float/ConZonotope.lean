import CORALean.ContSet.ConZonotope.Real.Instances
import CORALean.ContSet.HPolytope.Float.API
import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# Constrained zonotopes over a floating-point scalar: the representation

CORA's `conZonotope` with its centre, generators and coefficient constraints all
held in `𝕋`, plus the error box that makes it an `InflatedContSet`.

Two roundings, in two different places, and the rule is the same one the other
representations follow: pay where the representation already has slack of the
same kind. The centre and the generators have none — paying into them would grow
the order at every operation — so their rounding goes into the ambient box. The
constraints have slack in their bounds, so theirs goes into `P`, whose float form
carries an interval right-hand side.

One box, therefore, not two: `P` is a float `HPolytope` and does not nest a box
of its own.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

structure ConZonotope (𝕋 : Type) (n : ℕ) where
  h : ℕ
  c : Vec 𝕋 n
  G : Mat 𝕋 n h
  P : HPolytope 𝕋 h
  E : Interval 𝕋 n

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (ConZonotope 𝕋 n) (CORALean.Real.ConZonotope (Vec ℝ n)) 𝕋 n where
  -- generators transpose: stored as a matrix here, a family of vectors there
  nominal C := ⟨C.h, toRealVec C.c, fun j i => toReal (C.G i j), C.P.nominal⟩
  error C := C.E

/-- The nominal set spelt in this representation's own fields, so proofs never
mention `nominal` and every count reads `C.h`. -/
theorem ConZonotope.mem_nominalSet_iff [SoundFloatArithmetic 𝕋] {C : ConZonotope 𝕋 n}
    {x : Vec ℝ n} :
    x ∈ InflatedContSet.nominalSet C ↔ ∃ β : Vec ℝ C.h, (∀ j, |β j| ≤ 1)
      ∧ β ∈ C.P.construct
      ∧ ∀ i, x i = toReal (C.c i) + ∑ j, toReal (C.G i j) * β j :=
  Real.ConZonotope.mem_construct_iff

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev ConZonotope.construct [SoundFloatArithmetic 𝕋] (C : ConZonotope 𝕋 n) : Set (Vec ℝ n) :=
  InflatedContSet.construct C

end CORALean.Float
