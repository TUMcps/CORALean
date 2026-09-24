import CORALean.ContSet.Ellipsoid.Real.Instances
import CORALean.ContSet.InflatedContSet.InflatedContSet

/-!
# Ellipsoids over a floating-point scalar: the representation

The exact layer's centre and generator matrix held in `𝕋`, plus the error box
that makes it an `InflatedContSet`. Storing the generator matrix rather than
CORA's shape matrix pays here as it does over ℝ, and more: a shape matrix would
have to come back through a matrix square root, and this layer has no square
root of any kind.

No generator transpose, unlike the zonotope and the polynomial zonotope: the
exact `Ellipsoid` already stores `G` as a matrix, so the nominal part is the two
stored arrays read entrywise as reals.

What ranges over the unit ball is `u`, not a free coefficient — which changes
nothing about the rounding. `‖u‖₂ ≤ 1` gives `|uⱼ| ≤ 1`, so a rounded generator
costs exactly what a zonotope's does; `Theorems/MemGeneratorError` says why the
tighter bound is the one worth not taking.
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

structure Ellipsoid (𝕋 : Type) (n : ℕ) where
  /-- The generator count, as over ℝ: `G` is `n × k` and need not be square. -/
  k : ℕ
  q : Vec 𝕋 n
  G : Mat 𝕋 n k
  /-- The error box. Named `err` rather than `E`, which reads as an exponent
  matrix nowhere here but as the exact layer's ellipsoid everywhere. -/
  err : Interval (Vec 𝕋 n)

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (Ellipsoid 𝕋 n) (CORALean.Real.Ellipsoid n) 𝕋 n where
  nominal E := ⟨E.k, toRealVec E.q, toRealMat E.G⟩
  error E := E.err

/-! The nominal ellipsoid's fields, so proofs can see through the instance. -/

theorem Ellipsoid.nominal_k [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) :
    (InflatedContSet.nominal E).k = E.k := rfl

theorem Ellipsoid.nominal_q [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) :
    (InflatedContSet.nominal E).q = toRealVec E.q := rfl

theorem Ellipsoid.nominal_G [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) :
    (InflatedContSet.nominal E).G = toRealMat E.G := rfl

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev Ellipsoid.construct [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) : Set (Vec ℝ n) :=
  InflatedContSet.construct E

/-! ## Storage

Every field is a function type, so the ellipsoid an operation returns is a
closure over the one it was given. `materialise` stores them and `materialise_eq`
says it is the identity; `Global/Tensor` says why the vectors are built here. -/

def Ellipsoid.materialise (E : Ellipsoid 𝕋 n) : Ellipsoid 𝕋 n :=
  let q : Vector 𝕋 n := Vector.ofFn E.q
  let G : Vector (Vector 𝕋 E.k) n := Vector.ofFn fun i => Vector.ofFn fun j => E.G i j
  { k := E.k
    q := fun i => q[i.val]'i.isLt
    G := fun i j => (G[i.val]'i.isLt)[j.val]'j.isLt
    err := E.err.materialise }

omit [FloatOps 𝕋] in
@[simp] theorem Ellipsoid.materialise_eq (E : Ellipsoid 𝕋 n) : E.materialise = E := by
  simp [Ellipsoid.materialise]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
