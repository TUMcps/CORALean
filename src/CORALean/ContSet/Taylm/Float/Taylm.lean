module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.Taylm.Real.Taylm

@[expose] public section

/-!
# Taylor models over a floating-point scalar: the representation

CORA's `taylm` with its coefficients and remainder bounds in `𝕋`. The exponents stay in
ℕ, so the monomials are the exact layer's; rounding is paid where a coefficient is
computed, by storing one end of its enclosure and adding the width to the remainder, every
monomial being in `[-1, 1]` on the box. The remainder is the error box a float
representation elsewhere carries beside its nominal set: here the model already has one.

`nominal` reads the stored floats as an exact model, and a float model encloses what its
nominal model encloses.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Taylm (𝕋 : Type) (n : ℕ) where
  terms : List (𝕋 × (Fin n → ℕ))
  remInf : 𝕋
  remSup : 𝕋
  maxOrder : ℕ

section Reading

variable [SoundFloatArithmetic 𝕋]

def Taylm.nominal (T : Taylm 𝕋 n) : Real.Taylm n :=
  ⟨T.terms.map fun a => (SoundFloatArithmetic.toReal a.1, a.2),
    SoundFloatArithmetic.toReal T.remInf, SoundFloatArithmetic.toReal T.remSup, T.maxOrder⟩

/-- What a stored model claims: its nominal encloses `f`. The meaning of the float type, as
`construct` is of a set, and the hypothesis of every float Taylor-model theorem. -/
def Taylm.Encloses (T : Taylm 𝕋 n) (f : Vec ℝ n → ℝ) : Prop := T.nominal.Encloses f

/-- The set a vector of stored models encloses: its nominals'. There is no error box to inflate,
so this is the class's `construct`, spelt for `T.construct` to resolve. -/
def Taylm.construct {m : ℕ} (T : Fin m → Taylm 𝕋 n) : Set (Vec ℝ m) :=
  Real.Taylm.construct fun i => (T i).nominal

end Reading

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
