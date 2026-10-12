import CORALean.ContSet.SpectraShadow.Float.SpectraShadow
import CORALean.ContSet.SpectraShadow.Real.Definitions.ESumRep

/-!
# Existential sum representations over a floating-point scalar

CORA's hidden property `ESumRep = {B, C}` of a spectrahedral shadow, its matrices held in `𝕋`. The
set it stands for is the exact layer's, the matrices read entrywise as reals (`nominal`). There is
no error box: the matrices are stored, never computed from a rounded quantity, and what rounding
costs an operation that builds one is the operation's to state.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure SpectraShadow.ESumRep (𝕋 : Type) (n : ℕ) where
  k : ℕ
  q : ℕ
  B₀ : Mat 𝕋 k k
  B : Fin n → Mat 𝕋 k k
  C : Fin q → Mat 𝕋 k k

/-- The set a stored existential sum representation stands for: the exact layer's, the matrices
read entrywise as reals. -/
def SpectraShadow.ESumRep.construct [SoundFloatArithmetic 𝕋] (E : SpectraShadow.ESumRep 𝕋 n) :
    Set (Vec ℝ n) :=
  (⟨E.k, E.q, toRealMat E.B₀, fun i => toRealMat (E.B i), fun j => toRealMat (E.C j)⟩ :
    CORALean.Real.SpectraShadow.ESumRep n).construct

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
