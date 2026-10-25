module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# Intervals over a floating-point scalar: the representation

CORA's `interval` with the same `inf` and `sup`, held in `𝕋` rather than ℝ. Indexed by the ambient
type it stores, as the exact layer's `Interval α` is: `Interval (Vec 𝕋 n)` is a box, and
`Interval (Mat 𝕋 m n)` is CORA's `intervalMatrix`. `RealImage` says which real ambient type a stored
one denotes, and that is all `nominal` needs; the exact layer's `Entrywise` reads the result, so the
float layer needs no counterpart of that class. What it denotes is the exact layer's `construct` of
`nominal`, fixed by definition rather than by a lemma. Each operation then owes only enclosure.
The interval is the one [1, Sec. 2] introduces for CORA's `interval`, with its ends held in `𝕋`.
There is no `I_error` and no `absorbRounding`: the interval is the error-box type itself.

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A box between the stored lower bound `inf` and upper bound `sup`. -/
structure Interval (α : Type) where
  inf : α
  sup : α

/-- The exact interval the stored bounds describe, read through `RealImage`. -/
def Interval.nominal {α β : Type} [RealImage α β] (I : Interval α) :
    CORALean.Real.Interval β :=
  ⟨RealImage.realImage I.inf, RealImage.realImage I.sup⟩

/-- The set an interval of stored floats stands for: its nominal's. Without an error box there is
nothing to inflate, so this is the class's `construct`, spelt for `I.construct` to resolve. -/
def Interval.construct {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β]
    [Entrywise β ι] (I : Interval α) : Set β :=
  I.nominal.construct

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
