module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.materialise`

Both bounds are function types, so the interval an operation returns is a
closure over the one it was given and a loop pays for its whole history on every
read. `materialise` stores them, and `materialise_eq` says it is the identity,
so what it changes is only what running a definition costs. `Global/Tensor` says
why the vectors are built here rather than by a helper.

This is also the storage of five other representations, which carry an error box
of this type and materialise it through here.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.materialise (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  let lo : Vector 𝕋 n := Vector.ofFn I.inf
  let hi : Vector 𝕋 n := Vector.ofFn I.sup
  ⟨fun i => lo[i.val]'i.isLt, fun i => hi[i.val]'i.isLt⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
