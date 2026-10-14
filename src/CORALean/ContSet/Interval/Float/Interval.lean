module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# Intervals over a floating-point scalar: the representation

CORA's `interval` with the same `inf` and `sup`, held in `𝕋` rather than ℝ.

Indexed by the ambient type it stores, as the exact layer's `Interval α` is:
`Interval (Vec 𝕋 n)` is a box, and `Interval (Mat 𝕋 m n)` is CORA's
`intervalMatrix` with no separate representation. `RealImage` says which real
ambient type a stored one denotes, `Vec 𝕋 n` reading as `Vec ℝ n` and `Mat 𝕋 m n`
as `Mat ℝ m n`, and that is all `nominal` needs. The exact layer's `Entrywise`
then reads the result: nothing here is read coordinatewise in `𝕋`, so the float
layer needs no counterpart of that class.

What it denotes is the exact layer's `construct` of `nominal`, fixed by
definition rather than by a lemma. Each operation then owes only enclosure.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Interval (α : Type) where
  inf : α
  sup : α

def Interval.nominal {α β : Type} [RealImage α β] (I : Interval α) :
    CORALean.Real.Interval β :=
  ⟨RealImage.realImage I.inf, RealImage.realImage I.sup⟩

def Interval.construct {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β]
    [Entrywise β ι] (I : Interval α) : Set β :=
  I.nominal.construct

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
