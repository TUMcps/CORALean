module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.materialiseMat`

-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}
variable {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The same storage at `Mat 𝕋 m n`, needed once the interval-matrix chain
(`matMul`, `matPow`, `expIntervalTaylor`) starts nesting recursive calls: each
row is materialised, then the rows themselves. -/
def Interval.materialiseMat (I : Interval (Mat 𝕋 m n)) : Interval (Mat 𝕋 m n) :=
  let lo : Vector (Vector 𝕋 n) m := Vector.ofFn fun i => Vector.ofFn (I.inf i)
  let hi : Vector (Vector 𝕋 n) m := Vector.ofFn fun i => Vector.ofFn (I.sup i)
  ⟨fun i j => (lo[i.val]'i.isLt)[j.val]'j.isLt, fun i j => (hi[i.val]'i.isLt)[j.val]'j.isLt⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
