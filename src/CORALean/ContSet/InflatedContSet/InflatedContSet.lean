import CORALean.ContSet.Interval.Float.API

/-!
# Representations that carry a rounding error

A nominal representation inflated by an axis-aligned box holding what rounding
has cost so far. An operation never rounds its nominal part into shape: it
computes that part however it likes and pays the difference into the box.

For a zonotope that is what matters. Rounding paid into new generators would
grow the generator count on every operation, and generator count is what
reachability costs; paid into the box it does not.

`Interval` deliberately has no instance: it *is* the box, so an error term would
nest a box inside a box.

Boxes are built by whoever knows what was rounded — `Interval.residual`,
`Interval.symmetric`, `Zonotope.generatorError` — and none mentions this class.

Guarantees live in `Theorems`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

class InflatedContSet (S : Type) (N : outParam Type) (𝕋 : outParam Type) (n : outParam ℕ)
    [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ContSet N (Vec ℝ n)] where
  /-- The exact-layer representation the stored floats describe, not the set it
  denotes — keeping the representation is what lets a refinement proof reach the
  theorem about it. Not *exact*: the stored fields are rounded. -/
  nominal : S → N
  /-- Everything rounding has cost, as a box. Held in `𝕋`, since operations
  compute it; a real interval here could not be computed with. -/
  error : S → Interval 𝕋 n

namespace InflatedContSet

variable {𝕋 S N : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable [ContSet N (Vec ℝ n)] [InflatedContSet S N 𝕋 n]

/-- What the nominal part denotes. Generic code cannot write
`s.nominal.construct`: dot notation resolves through a head constant, and `N` is
a variable. Concrete proofs write `(nominal Z).construct`. -/
abbrev nominalSet (s : S) : Set (Vec ℝ n) := ContSet.construct (nominal s)

def construct (s : S) : Set (Vec ℝ n) := nominalSet s + (error s).construct

instance : ContSet S (Vec ℝ n) := ⟨construct⟩

end InflatedContSet

end CORALean.Float
