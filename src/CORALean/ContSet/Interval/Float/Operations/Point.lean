import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.point`, over a floating-point scalar

Zero width, which is the singleton the stored floats denote. Nothing is rounded:
the point is whatever `𝕋` already holds, and `mem_point` reads it back through
`toRealVec`.

Composed with `plus` this is a translation, so a layer needs no operation of its
own for a bias — which is how a linear layer's offset reaches a set here.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def Interval.point (v : Vec 𝕋 n) : Interval 𝕋 n := ⟨v, v⟩

-- both bounds are the stored vector, so each coordinate is bounded by equality
theorem Interval.mem_point [SoundFloatArithmetic 𝕋] (v : Vec 𝕋 n) :
    toRealVec v ∈ (Interval.point v).construct := fun _ => ⟨le_rfl, le_rfl⟩

end CORALean.Float
