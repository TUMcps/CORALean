import CORALean.ContSet.InflatedContSet.InflatedContSet
import CORALean.ContSet.PolyZonotope.Real.Instances

/-!
# Sparse polynomial zonotopes over a floating-point scalar: the representation

CORA's `polyZonotope` with its centre, dependent generators, exponent matrix and
independent generators, plus the error box that makes it an `InflatedContSet`.
The nominal part is the polynomial zonotope those stored floats describe; the
box holds what rounding has cost.

Only `c`, `G` and `GI` move to `𝕋`. The exponent matrix stays over ℕ, where
every operation on it — block-diagonal append, column addition, column
deletion — is exact, so the monomials of the nominal set are the exact layer's
monomials and not roundings of them. That is what makes the float layer's error
identical in kind to a zonotope's; `Theorems/MemGeneratorError` says what it
costs.

The error box is `err` rather than `E`, which the exponent matrix has taken.
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

structure PolyZonotope (𝕋 : Type) (n : ℕ) where
  /-- The dependent factors, shared across all of `G`. -/
  p : ℕ
  /-- The dependent generators. -/
  h : ℕ
  /-- The independent generators. -/
  q : ℕ
  c : Vec 𝕋 n
  G : Mat 𝕋 n h
  E : Fin p → Fin h → ℕ
  GI : Mat 𝕋 n q
  err : Interval 𝕋 n

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (PolyZonotope 𝕋 n) (CORALean.Real.PolyZonotope (Vec ℝ n)) 𝕋 n where
  -- generators transpose: stored as a matrix here, a family of vectors there
  nominal pZ := ⟨pZ.p, pZ.h, pZ.q, toRealVec pZ.c, fun l i => toReal (pZ.G i l), pZ.E,
    fun j i => toReal (pZ.GI i j)⟩
  error pZ := pZ.err

/-! The nominal set's fields, so proofs can see through the instance. -/

theorem PolyZonotope.nominal_p [SoundFloatArithmetic 𝕋] (pZ : PolyZonotope 𝕋 n) :
    (InflatedContSet.nominal pZ).p = pZ.p := rfl

theorem PolyZonotope.nominal_h [SoundFloatArithmetic 𝕋] (pZ : PolyZonotope 𝕋 n) :
    (InflatedContSet.nominal pZ).h = pZ.h := rfl

theorem PolyZonotope.nominal_q [SoundFloatArithmetic 𝕋] (pZ : PolyZonotope 𝕋 n) :
    (InflatedContSet.nominal pZ).q = pZ.q := rfl

theorem PolyZonotope.nominal_E [SoundFloatArithmetic 𝕋] (pZ : PolyZonotope 𝕋 n) :
    (InflatedContSet.nominal pZ).E = pZ.E := rfl

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev PolyZonotope.construct [SoundFloatArithmetic 𝕋] (pZ : PolyZonotope 𝕋 n) :
    Set (Vec ℝ n) := InflatedContSet.construct pZ

/-! ## Storage

Every field is a function type, so the representation an operation returns is a
closure over the one it was given. `materialise` stores them and `materialise_eq`
says it is the identity; `Global/Tensor` says why the vectors are built here.

`E` is stored along with the floats: it is a curried function rather than a
`Mat`, and `compact` reads it through two index maps, so it is where an
unstored exponent matrix costs the most. -/

def PolyZonotope.materialise (pZ : PolyZonotope 𝕋 n) : PolyZonotope 𝕋 n :=
  let c : Vector 𝕋 n := Vector.ofFn pZ.c
  let G : Vector (Vector 𝕋 pZ.h) n := Vector.ofFn fun i => Vector.ofFn fun l => pZ.G i l
  let E : Vector (Vector ℕ pZ.h) pZ.p := Vector.ofFn fun k => Vector.ofFn fun l => pZ.E k l
  let GI : Vector (Vector 𝕋 pZ.q) n := Vector.ofFn fun i => Vector.ofFn fun j => pZ.GI i j
  { p := pZ.p
    h := pZ.h
    q := pZ.q
    c := fun i => c[i.val]'i.isLt
    G := fun i l => (G[i.val]'i.isLt)[l.val]'l.isLt
    E := fun k l => (E[k.val]'k.isLt)[l.val]'l.isLt
    GI := fun i j => (GI[i.val]'i.isLt)[j.val]'j.isLt
    err := pZ.err.materialise }

omit [FloatOps 𝕋] in
@[simp] theorem PolyZonotope.materialise_eq (pZ : PolyZonotope 𝕋 n) : pZ.materialise = pZ := by
  simp [PolyZonotope.materialise]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
