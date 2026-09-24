import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.ContSet.Interval.Real.Interval

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

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   24-September-2026
-- Last revision: ---


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

/-! ## Storage

Both bounds are function types, so the interval an operation returns is a
closure over the one it was given and a loop pays for its whole history on every
read. `materialise` stores them, and `materialise_eq` says it is the identity,
so what it changes is only what running a definition costs. `Global/Tensor` says
why the vectors are built here rather than by a helper.

This is also the storage of five other representations, which carry an error box
of this type and materialise it through here. -/

def Interval.materialise (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  let lo : Vector 𝕋 n := Vector.ofFn I.inf
  let hi : Vector 𝕋 n := Vector.ofFn I.sup
  ⟨fun i => lo[i.val]'i.isLt, fun i => hi[i.val]'i.isLt⟩

omit [FloatOps 𝕋] in
@[simp] theorem Interval.materialise_eq (I : Interval (Vec 𝕋 n)) : I.materialise = I := by
  simp [Interval.materialise]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
