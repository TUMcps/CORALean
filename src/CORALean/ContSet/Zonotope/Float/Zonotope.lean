import CORALean.ContSet.InflatedContSet.InflatedContSet
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# Zonotopes over a floating-point scalar: the representation

CORA's `zonotope` with its centre and generators, plus the error box that makes
it an `InflatedContSet`. The nominal part is the zonotope those stored floats
describe; the box holds what rounding has cost.

`GZonotope α` is indexed by the ambient type it stores, as the exact layer's
`Zonotope α` and the float `Interval α` are, with generators a family rather than
a matrix: `GZonotope (Mat 𝕋 m n)` is CORA's `matZonotope`, with no separate
representation. `Zonotope 𝕋 n` is the vector case, a reducible abbreviation, so
the family `Zonotope 𝕋 : ℕ → Type` an algorithm is generic over keeps its
spelling. Its operations are named `Zonotope.*` and the matrix ones `GZonotope.*`,
dot notation reaching the latter from a vector zonotope by unfolding.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   09-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure GZonotope (α : Type) where
  h : ℕ
  c : α
  G : Fin h → α
  E : Interval α

abbrev Zonotope (𝕋 : Type) (n : ℕ) := GZonotope (Vec 𝕋 n)

/-- The exact zonotope the stored floats describe, read through `RealImage`. -/
abbrev GZonotope.nominal {α β : Type} [RealImage α β] (Z : GZonotope α) :
    CORALean.Real.Zonotope β :=
  ⟨Z.h, RealImage.realImage Z.c, fun j => RealImage.realImage (Z.G j)⟩

instance {α β : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] :
    InflatedContSet (GZonotope α) (CORALean.Real.Zonotope β) α β where
  nominal := GZonotope.nominal
  error Z := Z.E

/-! The nominal zonotope's fields, so proofs can see through the instance. -/

theorem Zonotope.nominal_h [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) :
    (InflatedContSet.nominal Z).h = Z.h := rfl

theorem Zonotope.nominal_c [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) :
    (InflatedContSet.nominal Z).c = toRealVec Z.c := rfl

theorem Zonotope.nominal_G [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) :
    (InflatedContSet.nominal Z).G = fun j i => toReal (Z.G j i) := rfl

/-- Inherited from `InflatedContSet`, at any ambient type: `nominal + E`. -/
abbrev GZonotope.construct {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β]
    [Entrywise β ι] (Z : GZonotope α) : Set β :=
  InflatedContSet.construct Z

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev Zonotope.construct [SoundFloatArithmetic 𝕋] (Z : Zonotope 𝕋 n) : Set (Vec ℝ n) :=
  InflatedContSet.construct Z

/-! ## Storage

Every field is a function type, so the zonotope an operation returns is a closure
over the one it was given, and a loop that iterates operations pays for its whole
history on every entry read. `materialise` stores the four fields; it is the
identity, which `materialise_eq` states and every proof downstream rewrites with,
so what it changes is only what running the definition costs. `Global/Tensor`
says why the vectors are built here rather than by a helper.

`Instances.lean` is where it is applied — an algorithm reaches a representation
through the operation classes and nowhere else, so materialising there bounds
every loop at once without a single operation or guarantee knowing about it. -/

def Zonotope.materialise (Z : Zonotope 𝕋 n) : Zonotope 𝕋 n :=
  let c : Vector 𝕋 n := Vector.ofFn Z.c
  let G : Vector (Vector 𝕋 n) Z.h := Vector.ofFn fun j => Vector.ofFn (Z.G j)
  { h := Z.h
    c := fun i => c[i.val]'i.isLt
    G := fun j i => (G[j.val]'j.isLt)[i.val]'i.isLt
    E := Z.E.materialise }

omit [FloatOps 𝕋] in
@[simp] theorem Zonotope.materialise_eq (Z : Zonotope 𝕋 n) : Z.materialise = Z := by
  simp [Zonotope.materialise]

variable {m : ℕ}

/-- The same storage at `Mat 𝕋 m n`, the matrix zonotope: centre, every generator and the
interval-matrix box. `matPow` and the Taylor sum apply it at each step. -/
def GZonotope.materialiseMat (Z : GZonotope (Mat 𝕋 m n)) : GZonotope (Mat 𝕋 m n) :=
  let c : Vector (Vector 𝕋 n) m := Vector.ofFn fun i => Vector.ofFn (Z.c i)
  let G : Vector (Vector (Vector 𝕋 n) m) Z.h :=
    Vector.ofFn fun k => Vector.ofFn fun i => Vector.ofFn (Z.G k i)
  { h := Z.h
    c := fun i j => (c[i.val]'i.isLt)[j.val]'j.isLt
    G := fun k i j => ((G[k.val]'k.isLt)[i.val]'i.isLt)[j.val]'j.isLt
    E := Z.E.materialiseMat }

omit [FloatOps 𝕋] in
@[simp] theorem GZonotope.materialiseMat_eq (Z : GZonotope (Mat 𝕋 m n)) :
    Z.materialiseMat = Z := by
  simp [GZonotope.materialiseMat]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
