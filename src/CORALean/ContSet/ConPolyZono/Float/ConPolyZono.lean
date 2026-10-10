import CORALean.ContSet.ConPolyZono.Real.Instances
import CORALean.ContSet.InflatedContSet.InflatedContSet

/-!
# Constrained polynomial zonotopes over a floating-point scalar: the representation

CORA's `conPolyZono` with its five counts, its two generator blocks and its
constraint system `A μ(α) ∈ b`, plus the error box that makes it an
`InflatedContSet`.

`A` and `b` move to `𝕋` and are read back exactly. That is sound because the
nominal set is *defined* as what the stored floats denote — the constraint of
the nominal set is the constraint those floats state, not a rounding of some
other one.

Rounding therefore has two channels. The centre and the generators have no
slack, so theirs goes into the ambient error box; the constraint bounds do, `b`
being an interval, so theirs goes into `b`, widened outward and hence enclosing.
`plus` and `mtimes` copy the constraint block and pay nothing; `intersection` and
`compact` need both at once. `intersection`'s agreement rows relate two nominal points as
far apart as their error boxes allow, and the rounding of `c₂ - c₁` is added to
that tolerance, downward on the low side and upward on the high.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure ConPolyZono (𝕋 : Type) (n : ℕ) where
  /-- The dependent factors, shared by the generators and the constraints. -/
  p : ℕ
  /-- The dependent generators. -/
  h : ℕ
  /-- The independent generators. -/
  q : ℕ
  /-- The constraints. -/
  m : ℕ
  /-- The constraint generators. -/
  s : ℕ
  c : Vec 𝕋 n
  G : Mat 𝕋 n h
  E : Fin p → Fin h → ℕ
  GI : Mat 𝕋 n q
  A : Mat 𝕋 m s
  /-- Interval-valued, as over ℝ, and this is one of the two places a float
  operation may pay its rounding. -/
  b : Interval (Vec 𝕋 m)
  EC : Fin p → Fin s → ℕ
  err : Interval (Vec 𝕋 n)

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (ConPolyZono 𝕋 n) (CORALean.Real.ConPolyZono (Vec ℝ n))
      (Vec 𝕋 n) (Vec ℝ n) where
  -- generators transpose: stored as a matrix here, a family of vectors there
  nominal cPZ := ⟨cPZ.p, cPZ.h, cPZ.q, cPZ.m, cPZ.s, toRealVec cPZ.c,
    fun l i => toReal (cPZ.G i l), cPZ.E, fun j i => toReal (cPZ.GI i j), toRealMat cPZ.A,
    cPZ.b.nominal, cPZ.EC⟩
  error cPZ := cPZ.err

/-- What this set's own factors must satisfy, spelt in its own fields: the
instance's constraint block unfolded, as the three equations below unfold the
rest of it. -/
def ConPolyZono.satisfies [SoundFloatArithmetic 𝕋] (cPZ : ConPolyZono 𝕋 n)
    (a : Fin cPZ.p → ℝ) : Prop :=
  Real.ConPolyZono.holds (toRealMat cPZ.A) cPZ.b.nominal cPZ.EC a

/-! The nominal set's fields, so proofs can see through the instance. -/

theorem ConPolyZono.nominal_A [SoundFloatArithmetic 𝕋] (cPZ : ConPolyZono 𝕋 n) :
    (InflatedContSet.nominal cPZ).A = toRealMat cPZ.A := rfl

theorem ConPolyZono.nominal_b [SoundFloatArithmetic 𝕋] (cPZ : ConPolyZono 𝕋 n) :
    (InflatedContSet.nominal cPZ).b = cPZ.b.nominal := rfl

theorem ConPolyZono.nominal_EC [SoundFloatArithmetic 𝕋] (cPZ : ConPolyZono 𝕋 n) :
    (InflatedContSet.nominal cPZ).EC = cPZ.EC := rfl

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev ConPolyZono.construct [SoundFloatArithmetic 𝕋] (cPZ : ConPolyZono 𝕋 n) :
    Set (Vec ℝ n) := InflatedContSet.construct cPZ

/-! ## Storage

Every field is a function type, so the representation an operation returns is a
closure over the one it was given. `materialise` stores them and `materialise_eq`
says it is the identity; `Global/Tensor` says why the vectors are built here.
Both exponent matrices are stored along with the floats, being curried functions
rather than `Mat`s. -/

def ConPolyZono.materialise (cPZ : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n :=
  let c : Vector 𝕋 n := Vector.ofFn cPZ.c
  let G : Vector (Vector 𝕋 cPZ.h) n := Vector.ofFn fun i => Vector.ofFn fun l => cPZ.G i l
  let E : Vector (Vector ℕ cPZ.h) cPZ.p := Vector.ofFn fun k => Vector.ofFn fun l => cPZ.E k l
  let GI : Vector (Vector 𝕋 cPZ.q) n := Vector.ofFn fun i => Vector.ofFn fun j => cPZ.GI i j
  let A : Vector (Vector 𝕋 cPZ.s) cPZ.m := Vector.ofFn fun i => Vector.ofFn fun l => cPZ.A i l
  let EC : Vector (Vector ℕ cPZ.s) cPZ.p := Vector.ofFn fun k => Vector.ofFn fun l => cPZ.EC k l
  -- every field now reads out of a stored vector, so nothing is left as a closure
  { p := cPZ.p
    h := cPZ.h
    q := cPZ.q
    m := cPZ.m
    s := cPZ.s
    c := fun i => c[i.val]'i.isLt
    G := fun i l => (G[i.val]'i.isLt)[l.val]'l.isLt
    E := fun k l => (E[k.val]'k.isLt)[l.val]'l.isLt
    GI := fun i j => (GI[i.val]'i.isLt)[j.val]'j.isLt
    A := fun i l => (A[i.val]'i.isLt)[l.val]'l.isLt
    b := cPZ.b.materialise
    EC := fun k l => (EC[k.val]'k.isLt)[l.val]'l.isLt
    err := cPZ.err.materialise }

omit [FloatOps 𝕋] in
@[simp] theorem ConPolyZono.materialise_eq (cPZ : ConPolyZono 𝕋 n) : cPZ.materialise = cPZ := by
  simp [ConPolyZono.materialise]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
