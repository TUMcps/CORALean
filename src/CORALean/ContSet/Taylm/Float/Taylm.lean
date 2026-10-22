module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# Taylor models over a floating-point scalar: the representation

CORA's `taylm` with its coefficients and remainder bounds in `𝕋`, and an error box `I_error` beside
the remainder (#185). The exponents stay in ℕ, so the monomials are the exact layer's. The remainder
`rem` holds what the exact layer's would, rounded outward. Rounding is paid where a coefficient is
computed, by storing one end of its enclosure, and the width, every monomial being in `[-1, 1]` on
the box, goes into the error box. `Taylm.absorbRounding` adds the box to the remainder, which a
product, whose cross terms multiply the remainders, does first. `nominal` reads the stored floats as
an exact model, its remainder `rem` alone; `inflated` is the same model with the box added to the
remainder.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A Taylor model over floats: a list of terms (coefficient, exponents), a remainder interval, the
error box `I_error`, and the order `maxOrder` that `times` truncates to. -/
structure Taylm (𝕋 : Type) (n : ℕ) where
  terms : List (𝕋 × (Fin n → ℕ))
  /-- The remainder, read through `inf` and `sup`, as over ℝ. -/
  rem : Interval 𝕋
  /-- The error box: what rounding the coefficients has cost so far, read through `inf` and
  `sup`. -/
  I_error : Interval 𝕋
  /-- The order `times` truncates to, CORA's `max_order`. -/
  maxOrder : ℕ

section Reading

variable [SoundFloatArithmetic 𝕋]

/-- The exact model the stored floats describe, its remainder `rem` alone. -/
def Taylm.nominal (T : Taylm 𝕋 n) : Real.Taylm n :=
  ⟨T.terms.map fun a => (SoundFloatArithmetic.toReal a.1, a.2),
    ⟨SoundFloatArithmetic.toReal T.rem.inf, SoundFloatArithmetic.toReal T.rem.sup⟩, T.maxOrder⟩

/-- The nominal model with the error box added to its remainder, exactly. -/
def Taylm.inflated (T : Taylm 𝕋 n) : Real.Taylm n :=
  ⟨T.terms.map fun a => (SoundFloatArithmetic.toReal a.1, a.2),
    ⟨SoundFloatArithmetic.toReal T.rem.inf + SoundFloatArithmetic.toReal T.I_error.inf,
      SoundFloatArithmetic.toReal T.rem.sup + SoundFloatArithmetic.toReal T.I_error.sup⟩,
    T.maxOrder⟩

/-- What a stored model claims: its inflated model encloses `f`. The meaning of the float type, as
`construct` is of a set, and the hypothesis of every float Taylor-model theorem. -/
def Taylm.Encloses (T : Taylm 𝕋 n) (f : Vec ℝ n → ℝ) : Prop := T.inflated.Encloses f

/-- The set a vector of stored models encloses: its inflated models'. -/
def Taylm.construct {m : ℕ} (T : Fin m → Taylm 𝕋 n) : Set (Vec ℝ m) :=
  Real.Taylm.construct fun i => (T i).inflated

end Reading

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
