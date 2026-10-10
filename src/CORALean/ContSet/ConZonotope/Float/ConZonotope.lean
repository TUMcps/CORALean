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
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure ConZonotope (𝕋 : Type) (n : ℕ) where
  h : ℕ
  c : Vec 𝕋 n
  G : Mat 𝕋 n h
  P : HPolytope 𝕋 h
  E : Interval (Vec 𝕋 n)

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (ConZonotope 𝕋 n) (CORALean.Real.ConZonotope (Vec ℝ n))
      (Vec 𝕋 n) (Vec ℝ n) where
  -- generators transpose: stored as a matrix here, a family of vectors there
  nominal cZ := ⟨cZ.h, toRealVec cZ.c, fun j i => toReal (cZ.G i j), cZ.P.nominal⟩
  error cZ := cZ.E

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev ConZonotope.construct [SoundFloatArithmetic 𝕋] (cZ : ConZonotope 𝕋 n) : Set (Vec ℝ n) :=
  InflatedContSet.construct cZ

/-! ## Storage

Every field is a function type, so the representation an operation returns is a
closure over the one it was given. `materialise` stores them and `materialise_eq`
says it is the identity; `Global/Tensor` says why the vectors are built here. The
constraint polytope goes through its own `materialise`. -/

def ConZonotope.materialise (cZ : ConZonotope 𝕋 n) : ConZonotope 𝕋 n :=
  let c : Vector 𝕋 n := Vector.ofFn cZ.c
  let G : Vector (Vector 𝕋 cZ.h) n := Vector.ofFn fun i => Vector.ofFn fun j => cZ.G i j
  { h := cZ.h
    c := fun i => c[i.val]'i.isLt
    G := fun i j => (G[i.val]'i.isLt)[j.val]'j.isLt
    P := cZ.P.materialise
    E := cZ.E.materialise }

omit [FloatOps 𝕋] in
@[simp] theorem ConZonotope.materialise_eq (cZ : ConZonotope 𝕋 n) : cZ.materialise = cZ := by
  simp [ConZonotope.materialise]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
