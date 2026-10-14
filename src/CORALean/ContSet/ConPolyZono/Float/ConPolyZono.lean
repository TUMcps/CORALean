module

public import CORALean.ContSet.ConPolyZono.Real.Instances
public import CORALean.ContSet.InflatedContSet.InflatedContSet

@[expose] public section

/-!
# Constrained polynomial zonotopes over a floating-point scalar: the representation

CORA's `conPolyZono` with its five counts, its two generator blocks and its
constraint system `A μ_R(α) ∈ b`, plus the error box that makes it an
`InflatedContSet`. `ConPolyZono 𝕋 α` is generic over its ambient type,
generators a family, as the exact layer's `ConPolyZono α` is; `𝕋` stays, the
constraint system being scalar at every ambient type. `ConPolyZono 𝕋 (Vec 𝕋 n)`
is the vector case.

`A` and `b` move to `𝕋` and are read back exactly: the nominal set is *defined*
as what the stored floats denote, so its constraint is the one they state.

Rounding therefore has two channels. The centre and the generators have no
slack, so theirs goes into the ambient error box; the constraint bounds do, `b`
being an interval, so theirs goes into `b`, widened outward and hence enclosing.
`plus` and `mtimes` copy the constraint block and pay nothing; `intersection` and
`compact` need both at once. `intersection`'s agreement rows relate two nominal points
as far apart as their error boxes allow, plus the rounding of `c₂ - c₁`, directed outward.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure ConPolyZono (𝕋 α : Type) where
  /-- The dependent factors, shared by the generators and the constraints. -/
  p : ℕ
  /-- The dependent generators. -/
  h : ℕ
  /-- The independent generators, `qI` of them. -/
  qI : ℕ
  /-- The constraints. -/
  m : ℕ
  /-- The constraint generators. -/
  q : ℕ
  c : α
  G : Fin h → α
  E : Fin p → Fin h → ℕ
  GI : Fin qI → α
  A : Mat 𝕋 m q
  /-- Interval-valued, as over ℝ, and this is one of the two places a float
  operation may pay its rounding. -/
  b : Interval (Vec 𝕋 m)
  /-- The constraint exponent matrix. -/
  R : Fin p → Fin q → ℕ
  I_error : Interval α

/-- The exact constrained polynomial zonotope the stored floats describe, read
through `RealImage`. -/
protected abbrev ConPolyZono.nominal {α β : Type} [RealImage α β] [SoundFloatArithmetic 𝕋]
    (cPZ : ConPolyZono 𝕋 α) : CORALean.Real.ConPolyZono β :=
  ⟨cPZ.p, cPZ.h, cPZ.qI, cPZ.m, cPZ.q, RealImage.realImage cPZ.c,
    fun l => RealImage.realImage (cPZ.G l), cPZ.E, fun j => RealImage.realImage (cPZ.GI j),
    toRealMat cPZ.A, cPZ.b.nominal, cPZ.R⟩

instance {α β : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] [SoundFloatArithmetic 𝕋] :
    InflatedContSet (ConPolyZono 𝕋 α) (CORALean.Real.ConPolyZono β) α β where
  nominal := ConPolyZono.nominal
  I_error cPZ := cPZ.I_error

/-- What this set's own factors must satisfy, spelt in its own fields: the
instance's constraint block unfolded, as the three equations below unfold the
rest of it. -/
def ConPolyZono.satisfies [SoundFloatArithmetic 𝕋] (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (a : Fin cPZ.p → ℝ) : Prop :=
  Real.ConPolyZono.holds (toRealMat cPZ.A) cPZ.b.nominal cPZ.R a

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev ConPolyZono.construct [SoundFloatArithmetic 𝕋] (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    Set (Vec ℝ n) := InflatedContSet.construct cPZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
