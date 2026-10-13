import CORALean.ContSet.InflatedContSet.InflatedContSet
import CORALean.ContSet.VPolytope.Real.Instances
import CORALean.ContSet.VPolytope.Real.Theorems.PerturbSubset

/-!
# Vertex descriptions over a floating-point scalar: the representation

CORA's `polytope` with `isVRep` set, its vertices held in `𝕋`, plus the error box
that makes it an `InflatedContSet`.

The box is the only sound place to pay. Rounding a vertex moves a point, and
there is no direction to move it that enlarges the hull — a hull has no centre
to move away from — so what rounding costs cannot be absorbed into the vertices
the way an interval absorbs it into its bounds.

`VPolytope α` is generic over its ambient type, vertices a family, as the exact
layer's `VPolytope α` is; `VPolytope (Vec 𝕋 n)` is the vector case, and the
nominal reading copies the family.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure VPolytope (α : Type) where
  k : ℕ
  V : Fin k → α
  E : Interval α


/-- The exact vertex list the stored floats describe, read through `RealImage`. -/
protected abbrev VPolytope.nominal {α β : Type} [RealImage α β] (P : VPolytope α) :
    CORALean.Real.VPolytope β :=
  ⟨P.k, fun l => RealImage.realImage (P.V l)⟩

instance {α β : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] :
    InflatedContSet (VPolytope α) (CORALean.Real.VPolytope β) α β where
  nominal := VPolytope.nominal
  error P := P.E

/-- The nominal vertex list, so proofs can see through the instance. Through it
every count is `P.k`, where going via the instance gives the equal-but-distinct
`(nominal P).k`. -/
theorem VPolytope.nominal_eq [SoundFloatArithmetic 𝕋] (P : VPolytope (Vec 𝕋 n)) :
    InflatedContSet.nominal P
      = CORALean.Real.VPolytope.mk P.k (fun l i => toReal (P.V l i)) := rfl

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev VPolytope.construct [SoundFloatArithmetic 𝕋] (P : VPolytope (Vec 𝕋 n)) : Set (Vec ℝ n) :=
  InflatedContSet.construct P

/-! ## Storage

Every field is a function type, so the polytope an operation returns is a closure
over the one it was given. `materialise` stores them and `materialise_eq` says it
is the identity; `Global/Tensor` says why the vectors are built here. -/

def VPolytope.materialise (P : VPolytope (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) :=
  let V : Vector (Vector 𝕋 n) P.k := Vector.ofFn fun l => Vector.ofFn (P.V l)
  { k := P.k
    V := fun l i => (V[l.val]'l.isLt)[i.val]'i.isLt
    E := P.E.materialise }

omit [FloatOps 𝕋] in
@[simp] theorem VPolytope.materialise_eq (P : VPolytope (Vec 𝕋 n)) : P.materialise = P := by
  simp [VPolytope.materialise]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
