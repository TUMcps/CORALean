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

Vertices are stored as the columns of a matrix, as a zonotope's generators are,
and the nominal reading transposes.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

structure VPolytope (𝕋 : Type) (n : ℕ) where
  k : ℕ
  V : Mat 𝕋 n k
  E : Interval 𝕋 n

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (VPolytope 𝕋 n) (CORALean.Real.VPolytope (Vec ℝ n)) 𝕋 n where
  nominal P := ⟨P.k, fun l i => toReal (P.V i l)⟩
  error P := P.E

/-- The nominal vertex list, so proofs can see through the instance. Through it
every count is `P.k`, where going via the instance gives the equal-but-distinct
`(nominal P).k`. -/
theorem VPolytope.nominal_eq [SoundFloatArithmetic 𝕋] (P : VPolytope 𝕋 n) :
    InflatedContSet.nominal P
      = CORALean.Real.VPolytope.mk P.k (fun l i => toReal (P.V i l)) := rfl

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev VPolytope.construct [SoundFloatArithmetic 𝕋] (P : VPolytope 𝕋 n) : Set (Vec ℝ n) :=
  InflatedContSet.construct P

/-! ## Storage

Every field is a function type, so the polytope an operation returns is a closure
over the one it was given. `materialise` stores them and `materialise_eq` says it
is the identity; `Global/Tensor` says why the vectors are built here. -/

def VPolytope.materialise (P : VPolytope 𝕋 n) : VPolytope 𝕋 n :=
  let V : Vector (Vector 𝕋 P.k) n := Vector.ofFn fun i => Vector.ofFn fun l => P.V i l
  { k := P.k
    V := fun i l => (V[i.val]'i.isLt)[l.val]'l.isLt
    E := P.E.materialise }

omit [FloatOps 𝕋] in
@[simp] theorem VPolytope.materialise_eq (P : VPolytope 𝕋 n) : P.materialise = P := by
  simp [VPolytope.materialise]

end CORALean.Float
