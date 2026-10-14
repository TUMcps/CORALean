module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Le
public import CORALean.Global.Float.Instances.Flint.Flint

@[expose] public section

/-!
# `Global/Float/Instances/Flint/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

namespace Flint

variable {p : ℕ}


-- ==========================================  `half`  ========================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Exact and pure Lean: the exponent drops by one and the mantissa is untouched,
as in `Dyadic.half`. -/
def half (a : Flint p) : Flint p := ⟨a.mantissa, a.exponent - 1⟩


-- ===========================================  `le`  =========================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Exact and pure Lean: `Dyadic.le` of the same pairs, which aligns the two to
their common exponent and compares integers. -/
def le (a b : Flint p) : Bool := Dyadic.le a.toDyadic b.toDyadic


-- ========================================  `maximum`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `le` decides it exactly, so this picks one of its two arguments and rounds
nothing. -/
def maximum (a b : Flint p) : Flint p := if le a b then b else a


-- ========================================  `minimum`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `le` decides it exactly, so this picks one of its two arguments and rounds
nothing. -/
def minimum (a b : Flint p) : Flint p := if le a b then a else b


-- ==========================================  `neg`  =========================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Exact and pure Lean: the sign of the mantissa flips and nothing is rounded, so
FLINT is not asked. -/
def neg (a : Flint p) : Flint p := ⟨-a.mantissa, a.exponent⟩

end Flint
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
