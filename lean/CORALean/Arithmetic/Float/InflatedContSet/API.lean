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

`nominal` is deliberately not called *exact*: the stored centre and generators
are themselves rounded values, and `Arithmetic.Real` has already claimed that
word. The class carries the nominal part only as the set it denotes. Refinement
proofs still need its *representation* to invoke `Arithmetic.Real`, but each has
its own `toExact` for that, and asking for it here would need the representation
type as a further parameter for no gain.

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

class InflatedContSet (S : Type) (F : outParam Type) (n : outParam ℕ)
    [FloatOps F] [SoundFloatArithmetic F] where
  /-- What the nominal part denotes, before inflation. -/
  nominal : S → Set (Vec ℝ n)
  /-- Everything rounding has cost, as a box in the same coordinates. -/
  error : S → Interval F n

namespace InflatedContSet

variable {F S : Type} [FloatOps F] [SoundFloatArithmetic F] {n : ℕ}
variable [InflatedContSet S F n]

def construct (s : S) : Set (Vec ℝ n) := nominal s + (error s).construct

instance : ContSet S n := ⟨construct⟩

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
