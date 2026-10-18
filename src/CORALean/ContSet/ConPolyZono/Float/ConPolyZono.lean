module

public import CORALean.ContSet.ConPolyZono.Real.Instances
public import CORALean.ContSet.ConPolyZono.Real.Operations.Relax
public import CORALean.ContSet.InflatedContSet.InflatedContSet

@[expose] public section

/-!
# Constrained polynomial zonotopes over a floating-point scalar: the representation

CORA's `conPolyZono` [1, Def. 5] with its five counts, its two generator blocks and its
constraint system `A μ_R(α) = b`, plus the error box that makes it an `InflatedContSet`.
`ConPolyZono 𝕋 α` is generic over its ambient type, generators a family, as the exact layer's
`ConPolyZono α` is; `𝕋` stays, the constraint system being scalar at every ambient type.

`A` and `b` move to `𝕋` and are read back exactly: the nominal set is *defined*
as what the stored floats describe, so its constraint is the one they state.

Rounding has two channels. The center and the generators go into the ambient error box
`I_error`; a constraint row, an equation with no interior to absorb an error, records its own in
the per-row slack `b_error`, row `i` holding `|(A μ_R(α))ᵢ - bᵢ| ≤ |b_errorᵢ|`, as a float
`HPolytope` records its rows'. The nominal set is the exact `ConPolyZono` with `=` rows that
slack denotes, one slack factor per row (`Real.ConPolyZono.relax`); with no slack it is the stored
fields' own (`Real.ConPolyZono.relax_zero_construct`). `plus` and `mtimes` copy the
constraint block and pay nothing; `intersection` and `compact` need both channels at once.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
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
  b : Vec 𝕋 m
  /-- The slack of the constraint rows: row `i` holds `|(A μ_R(α))ᵢ - bᵢ| ≤ |b_errorᵢ|`. -/
  b_error : Vec 𝕋 m
  /-- The constraint exponent matrix. -/
  R : Fin p → Fin q → ℕ
  /-- The error box: what rounding has cost in the ambient space. -/
  I_error : Interval α

/-- The stored floats read back through `RealImage`, every row an equation: the constrained
polynomial zonotope they describe before the slack. -/
protected abbrev ConPolyZono.nominalCore {α β : Type} [RealImage α β] [SoundFloatArithmetic 𝕋]
    (cPZ : ConPolyZono 𝕋 α) : CORALean.Real.ConPolyZono β :=
  ⟨cPZ.p, cPZ.h, cPZ.qI, cPZ.m, cPZ.q, RealImage.realImage cPZ.c,
    fun l => RealImage.realImage (cPZ.G l), cPZ.E, fun j => RealImage.realImage (cPZ.GI j),
    toRealMat cPZ.A, toRealVec cPZ.b, cPZ.R⟩

/-- The exact constrained polynomial zonotope the stored floats describe: `nominalCore` with
each row relaxed by its slack. -/
protected abbrev ConPolyZono.nominal {α β : Type} [RealImage α β] [SoundFloatArithmetic 𝕋]
    (cPZ : ConPolyZono 𝕋 α) : CORALean.Real.ConPolyZono β :=
  CORALean.Real.ConPolyZono.relax cPZ.nominalCore (toRealVec cPZ.b_error)

instance {α β : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] [SoundFloatArithmetic 𝕋] :
    InflatedContSet (ConPolyZono 𝕋 α) (CORALean.Real.ConPolyZono β) α β where
  nominal := ConPolyZono.nominal
  I_error cPZ := cPZ.I_error

/-- What this set's own factors must satisfy, spelt in its own fields: every row met to within
its slack. -/
def ConPolyZono.satisfies [SoundFloatArithmetic 𝕋] (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (a : Fin cPZ.p → ℝ) : Prop :=
  ∀ i, |(toRealMat cPZ.A *ᵥ Real.PolyZonotope.monomial cPZ.R a) i - toReal (cPZ.b i)|
    ≤ |toReal (cPZ.b_error i)|

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev ConPolyZono.construct [SoundFloatArithmetic 𝕋] (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    Set (Vec ℝ n) := InflatedContSet.construct cPZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
