module

public import CORALean.ContSet.InflatedContSet.Interfaces
public import CORALean.ContSet.SpectraShadow.Real.Instances

@[expose] public section

/-!
# Spectrahedral shadows over a floating-point scalar: the representation

The exact layer's linear matrix inequality, center and generators held in `𝕋`, plus the error box
that makes it an `InflatedContSet`. The nominal part is the shadow those stored floats describe.
`SpectraShadow 𝕋 α` is generic over its ambient type, as the exact layer's is; `𝕋` stays, the
inequality's matrices being scalar at every ambient type. Nothing about the inequality rounds: its
matrices are stored, never computed, and the only arithmetic is on the center, whose rounding the
box absorbs. A rounded *generator* would not be absorbable, the variables `β` being unbounded, so
`mtimes` never multiplies two stored matrices: it ties the point to new free variables by equalities
in the inequality and multiplies only the error box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A spectrahedral shadow over floats: the points `c + Σ βᵢ Gᵢ` over coefficients `β` with `A₀ + Σ
βᵢ Aᵢ` positive semidefinite, and the error box `I_error`. -/
structure SpectraShadow (𝕋 α : Type) where
  /-- The size of the matrices in the inequality. -/
  k : ℕ
  /-- The number of free variables, and of generators. -/
  m : ℕ
  A₀ : Mat 𝕋 k k
  A : Fin m → Mat 𝕋 k k
  c : α
  G : Fin m → α
  I_error : Interval α

/-- The exact shadow the stored floats describe, read through `RealImage`. -/
protected abbrev SpectraShadow.nominal {α β : Type} [RealImage α β] [SoundFloatArithmetic 𝕋]
    (S : SpectraShadow 𝕋 α) : CORALean.Real.SpectraShadow β :=
  ⟨S.k, S.m, toRealMat S.A₀, fun i => toRealMat (S.A i), RealImage.realImage S.c,
    fun j => RealImage.realImage (S.G j)⟩

/-- A float spectrahedral shadow inflates the real one its stored floats describe, the `nominal`
one. -/
instance {α β : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] [SoundFloatArithmetic 𝕋] :
    InflatedContSet (SpectraShadow 𝕋 α) (CORALean.Real.SpectraShadow β) α β where
  nominal := SpectraShadow.nominal
  I_error S := S.I_error

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev SpectraShadow.construct [SoundFloatArithmetic 𝕋] (S : SpectraShadow 𝕋 (Vec 𝕋 n)) :
    Set (Vec ℝ n) :=
  InflatedContSet.construct S

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
