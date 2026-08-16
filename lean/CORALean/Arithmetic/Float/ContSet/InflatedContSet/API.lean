import CORALean.Arithmetic.Float.ContSet.Interval.Theorems

/-!
# Representations that carry a rounding error

Every floating-point representation but one is a nominal representation inflated
by an axis-aligned box holding what rounding has cost so far. The box is the
cheap part to keep sound — rounding a bound outward is one directed operation —
so an operation never rounds its nominal part into shape: it computes that part
however it likes and pays the difference into the box.

For a zonotope this is the difference that matters. Rounding error absorbed into
new generators would grow the generator count on every operation, and generator
count is what reachability costs; absorbed into the box it does not.

`Interval` is the exception, and deliberately has no instance: it *is* the box,
its bounds round outward directly, and giving it an error term would nest a box
inside a box.

`nominal` is a representation from `Arithmetic.Real`, not the set it denotes:
what a representation means is `s.nominal.construct`. Keeping the representation
rather than only its denotation is what lets a refinement proof reach the exact
layer's theorem about it. The word is deliberately not *exact* — the stored
centre and generators are themselves rounded values, and `Arithmetic.Real` has
already claimed that word.

What a representation denotes is `s.nominal.construct`. Generic code cannot say
it that way — dot notation resolves through a type's head constant and `N` is a
variable — so `nominalSet` names it instead. It is reducible, so the two are
interchangeable, and a representation's own proofs, where `N` is concrete, write
`(nominal Z).construct`.

`residual` and `generatorError` are the two ways a nominal part can be wrong: a
stored vector that should have been something else, and a stored matrix whose
coefficients are then scaled by something in `[-1, 1]`.

Guarantees live in `Theorems`.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float

open Pointwise FloatOps SoundFloatArithmetic

class InflatedContSet (S : Type) (N : outParam Type) (F : outParam Type) (n : outParam ℕ)
    [FloatOps F] [SoundFloatArithmetic F] [Real.ContSet N n] where
  /-- The exact-layer representation the stored floats describe. -/
  nominal : S → N
  /-- Everything rounding has cost, as a box in the same coordinates. -/
  error : S → Interval F n

namespace InflatedContSet

variable {F S N : Type} [FloatOps F] [SoundFloatArithmetic F] {n : ℕ}
variable [Real.ContSet N n] [InflatedContSet S N F n]

/-- What the nominal part denotes. -/
abbrev nominalSet (s : S) : Set (Vec ℝ n) := Real.ContSet.construct (nominal s)

def construct (s : S) : Set (Vec ℝ n) := nominalSet s + (error s).construct

instance : Real.ContSet S n := ⟨construct⟩

/-- The intended vector lies in `[lo, hi]` but `stored` was written down; this is
what has to be added back. -/
def residual (lo hi stored : Vec F n) : Interval F n :=
  ⟨fun i => subDown (lo i) (stored i), fun i => subUp (hi i) (stored i)⟩

/-- A matrix known only entrywise to within `d`, whose coefficients then range
over `[-1, 1]`, costs this symmetric box: each row sums, because every
coefficient can conspire. Named for the zonotope case, but nothing here is
specific to generators. -/
def generatorError {h : ℕ} (d : Mat F n h) : Interval F n :=
  ⟨fun i => neg (sumUp fun j => d i j), fun i => sumUp fun j => d i j⟩

end InflatedContSet

end CORALean.Arithmetic.Float
