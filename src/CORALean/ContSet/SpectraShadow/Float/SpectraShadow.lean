import CORALean.ContSet.InflatedContSet.InflatedContSet
import CORALean.ContSet.SpectraShadow.Real.Instances

/-!
# Spectrahedral shadows over a floating-point scalar: the representation

The exact layer's linear matrix inequality, centre and generators held in `𝕋`,
plus the error box that makes it an `InflatedContSet`. The nominal part is the
shadow those stored floats describe, the matrices read entrywise as reals.
`GSpectraShadow 𝕋 α` is generic over its ambient type, generators a family, as the
exact layer's `SpectraShadow α` is; `𝕋` stays, the inequality's matrices being
scalar at every ambient type. `SpectraShadow 𝕋 n` is the reducible vector case.

Nothing about the inequality rounds: its matrices are stored, never computed, and the
only arithmetic is on the centre, whose rounding the box absorbs. A rounded *generator*
would not be absorbable, the variables `β` being unbounded, so `mtimes` never multiplies
two stored matrices: it ties the point to new free variables by equalities in the
inequality and multiplies only the error box. A solver's own rounding is the caller's
to certify.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   10-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure GSpectraShadow (𝕋 α : Type) where
  /-- The size of the matrices in the inequality. -/
  k : ℕ
  /-- The number of free variables, and of generators. -/
  m : ℕ
  A₀ : Mat 𝕋 k k
  A : Fin m → Mat 𝕋 k k
  c : α
  G : Fin m → α
  E : Interval α

abbrev SpectraShadow (𝕋 : Type) (n : ℕ) := GSpectraShadow 𝕋 (Vec 𝕋 n)

/-- The exact shadow the stored floats describe, read through `RealImage`. -/
abbrev GSpectraShadow.nominal {α β : Type} [RealImage α β] [SoundFloatArithmetic 𝕋]
    (S : GSpectraShadow 𝕋 α) : CORALean.Real.SpectraShadow β :=
  ⟨S.k, S.m, toRealMat S.A₀, fun i => toRealMat (S.A i), RealImage.realImage S.c,
    fun j => RealImage.realImage (S.G j)⟩

instance {α β : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] [SoundFloatArithmetic 𝕋] :
    InflatedContSet (GSpectraShadow 𝕋 α) (CORALean.Real.SpectraShadow β) α β where
  nominal := GSpectraShadow.nominal
  error S := S.E

/-! The nominal shadow's fields, so proofs can see through the instance. -/

theorem SpectraShadow.nominal_c [SoundFloatArithmetic 𝕋] (S : SpectraShadow 𝕋 n) :
    (InflatedContSet.nominal S).c = toRealVec S.c := rfl

theorem SpectraShadow.nominal_G [SoundFloatArithmetic 𝕋] (S : SpectraShadow 𝕋 n) :
    (InflatedContSet.nominal S).G = fun j i => toReal (S.G j i) := rfl

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev SpectraShadow.construct [SoundFloatArithmetic 𝕋] (S : SpectraShadow 𝕋 n) :
    Set (Vec ℝ n) :=
  InflatedContSet.construct S

/-! ## Storage

Every field is a function type, so the shadow an operation returns is a closure
over the one it was given. `materialise` stores them and `materialise_eq` says it
is the identity; `Global/Tensor` says why the vectors are built here. -/

def SpectraShadow.materialise (S : SpectraShadow 𝕋 n) : SpectraShadow 𝕋 n :=
  let A₀ : Vector (Vector 𝕋 S.k) S.k := Vector.ofFn fun i => Vector.ofFn fun j => S.A₀ i j
  let A : Vector (Vector (Vector 𝕋 S.k) S.k) S.m :=
    Vector.ofFn fun l => Vector.ofFn fun i => Vector.ofFn fun j => S.A l i j
  let c : Vector 𝕋 n := Vector.ofFn S.c
  let G : Vector (Vector 𝕋 n) S.m := Vector.ofFn fun j => Vector.ofFn (S.G j)
  { k := S.k
    m := S.m
    A₀ := fun i j => (A₀[i.val]'i.isLt)[j.val]'j.isLt
    A := fun l i j => ((A[l.val]'l.isLt)[i.val]'i.isLt)[j.val]'j.isLt
    c := fun i => c[i.val]'i.isLt
    G := fun j i => (G[j.val]'j.isLt)[i.val]'i.isLt
    E := S.E.materialise }

omit [FloatOps 𝕋] in
@[simp] theorem SpectraShadow.materialise_eq (S : SpectraShadow 𝕋 n) : S.materialise = S := by
  simp [SpectraShadow.materialise]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
