module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# Representations that carry a rounding error

A nominal representation inflated by an axis-aligned box holding what rounding has cost so far. An
operation never rounds its nominal part into shape: it computes that part however it likes and pays
the difference into the box. Indexed by the stored ambient type `α` and the real one `β` it reads as
(`RealImage`), as `Interval` is: `Vec 𝕋 n` over `Vec ℝ n`, or `Mat 𝕋 m n` over `Mat ℝ m n`. For a
zonotope that is the point: rounding paid into new generators would grow the generator count on
every operation. `Interval` deliberately has no instance: it *is* the box. Boxes are built by
whoever knows what was rounded (`Interval.residual`, `Interval.symmetric`,
`Zonotope.generatorError`).
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   09-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic


-- ========================================  MAIN TYPE  ========================================= --

/-- A float representation `S` whose stored data describe an exact representation `N` (`nominal`) up
to a rounding error box `I_error`; it denotes the nominal set plus the box. -/
class InflatedContSet (S : Type) (N : outParam Type) (α : outParam Type) (β : outParam Type)
    [RealImage α β] [AddCommGroup β] [Module ℝ β] [ContSet N β] where
  /-- The exact-layer representation the stored floats describe, not the set it
  denotes — keeping the representation is what lets a refinement proof reach the
  theorem about it. -/
  nominal : S → N
  /-- Everything rounding has cost, as a box. Held in `α`, the stored ambient
  type, because operations compute it. -/
  I_error : S → Interval α

namespace InflatedContSet

variable {S N α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] [Entrywise β ι]
variable [ContSet N β] [InflatedContSet S N α β]

/-- What the nominal part denotes. Generic code cannot write
`s.nominal.construct`, since dot notation resolves through a head constant and
`N` is a variable. -/
abbrev nominalSet (s : S) : Set β := ContSet.construct (nominal s)

/-- The set an inflated representation denotes: the nominal set plus the error box. -/
def construct (s : S) : Set β := nominalSet s + (I_error s).construct

/-- An inflated representation denotes `InflatedContSet.construct`. -/
instance : ContSet S β := ⟨construct⟩

end InflatedContSet

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
