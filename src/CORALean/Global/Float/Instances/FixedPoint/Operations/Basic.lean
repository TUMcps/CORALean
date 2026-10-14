module

public import CORALean.Global.Float.Instances.FixedPoint.FixedPoint
public import CORALean.Global.Float.Instances.FixedPoint.Operations.ExactAdd
public import CORALean.Global.Float.Instances.FixedPoint.Operations.RoundDown
public import CORALean.Global.Float.Instances.FixedPoint.Operations.RoundUp

@[expose] public section

/-!
# `Global/Float/Instances/FixedPoint/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

namespace FixedPoint

variable {f : ℕ}


-- ========================================  `addDown`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `exactAdd`, then `roundDown` back to `f` digits. -/
def addDown (a b : FixedPoint f) : FixedPoint f := roundDown (exactAdd a b)


-- =========================================  `addUp`  ========================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `exactAdd`, then `roundUp` back to `f` digits. -/
def addUp (a b : FixedPoint f) : FixedPoint f := roundUp (exactAdd a b)


-- =========================================  `divUp`  ========================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `divDown`'s mirror: negates the shifted dividend twice, turning the floor into
a ceiling exactly as `roundUp` does. -/
def divUp (a b : FixedPoint f) : FixedPoint f :=
  ⟨-(-(a.m * 10 ^ (b.d + f)) / (10 ^ a.d * b.m)), f⟩


-- ========================================  `exactMul`  ======================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Closed on fixed-point values: only the mantissa grows and the digit counts
add. `MulUp`/`MulDown` round it back down to `f`. -/
def exactMul (a b : FixedPoint f) : FixedPoint f := ⟨a.m * b.m, a.d + b.d⟩


-- ===========================================  `le`  =========================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Exact, and needing no rounding: cross-multiplied by the other side's power of
ten, two values at different digit counts compare the same way their exact
rationals do, with nothing to align first. -/
def le (a b : FixedPoint f) : Bool := a.m * 10 ^ b.d ≤ b.m * 10 ^ a.d


-- ========================================  `maximum`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `le` decides it exactly, so this picks one of its two arguments and rounds
nothing. -/
def maximum (a b : FixedPoint f) : FixedPoint f := if le a b then b else a


-- ========================================  `minimum`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `le` decides it exactly, so this picks one of its two arguments and rounds
nothing. -/
def minimum (a b : FixedPoint f) : FixedPoint f := if le a b then a else b


-- ========================================  `mulDown`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `exactMul`, then `roundDown` back to `f` digits. -/
def mulDown (a b : FixedPoint f) : FixedPoint f := roundDown (exactMul a b)


-- =========================================  `mulUp`  ========================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `exactMul`, then `roundUp` back to `f` digits. -/
def mulUp (a b : FixedPoint f) : FixedPoint f := roundUp (exactMul a b)


-- ==========================================  `neg`  =========================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Exact: flips the mantissa's sign and leaves the digit count alone. -/
def neg (x : FixedPoint f) : FixedPoint f := ⟨-x.m, x.d⟩

end FixedPoint
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
