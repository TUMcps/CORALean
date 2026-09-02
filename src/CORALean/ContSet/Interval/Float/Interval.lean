import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.ContSet.Interval.Real.Interval

/-!
# Intervals over a floating-point scalar: the representation

CORA's `interval` with the same `inf` and `sup`, held in `𝕋` rather than ℝ.

What it denotes is the exact layer's `construct` of `nominal`, fixed by
definition rather than by a lemma. Each operation then owes only enclosure.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   18-August-2026
-- Last revision: ---

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

structure Interval (𝕋 : Type) (n : ℕ) where
  inf : Vec 𝕋 n
  sup : Vec 𝕋 n

def Interval.nominal [SoundFloatArithmetic 𝕋] (I : Interval 𝕋 n) :
    CORALean.Real.Interval (Vec ℝ n) :=
  ⟨toRealVec I.inf, toRealVec I.sup⟩

def Interval.construct [SoundFloatArithmetic 𝕋] (I : Interval 𝕋 n) : Set (Vec ℝ n) :=
  I.nominal.construct

end CORALean.Float
