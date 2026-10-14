module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Basic
public import CORALean.Global.Float.Instances.Dyadic.Operations.ExactAdd
public import CORALean.Global.Float.Instances.Dyadic.Operations.Le
public import CORALean.Global.Float.Instances.IEEE.IEEE

@[expose] public section

/-!
# `Global/Float/Instances/IEEE/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- =======================================  `gridShift`  ======================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

namespace IEEE

variable {fmt : IEEEFormat}

/-- Enough to leave `p` bits, which is `Dyadic.shift`, and enough to raise the exponent to the
smallest subnormal's, `qmin`, whichever is more. The second is what makes a result below the
normal range land on the subnormal grid, where IEEE 754 keeps a fixed step rather than `p` bits. -/
def gridShift (d : Dyadic fmt.p) : ℕ := max d.shift (fmt.qmin - d.exponent).toNat

end IEEE

end CORALean.Float


-- ===========================================  `le`  =========================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

namespace IEEE

variable {fmt : IEEEFormat}

/-- Exact: `Dyadic.le`, which compares the mantissas at the common exponent. -/
def le (a b : IEEE fmt) : Bool := Dyadic.le a.toDyadic b.toDyadic

end IEEE

end CORALean.Float


-- ========================================  `maximum`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

namespace IEEE

variable {fmt : IEEEFormat}

/-- `le` decides it exactly, so this picks an argument and rounds nothing. -/
def maximum (a b : IEEE fmt) : IEEE fmt := if le a b then b else a

end IEEE

end CORALean.Float


-- ========================================  `minimum`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

namespace IEEE

variable {fmt : IEEEFormat}

/-- `le` decides it exactly, so this picks an argument and rounds nothing. -/
def minimum (a b : IEEE fmt) : IEEE fmt := if le a b then a else b

end IEEE

end CORALean.Float


-- ==========================================  `neg`  =========================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

namespace IEEE

variable {fmt : IEEEFormat}

/-- Exact: every format is symmetric about zero, so the grid is too. -/
def neg (x : IEEE fmt) : IEEE fmt := ⟨-x.mantissa, x.exponent⟩

end IEEE

end CORALean.Float


-- =======================================  `roundDown`  ======================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

namespace IEEE

variable {fmt : IEEEFormat}

/-- Integer `/` floors for a positive divisor, so dropping `gridShift` bits and raising the
exponent to match rounds toward `-∞`, onto the grid of `fmt`. -/
def roundDown (d : Dyadic fmt.p) : IEEE fmt :=
  let k := gridShift d
  ⟨d.mantissa / 2 ^ k, d.exponent + k⟩

end IEEE

end CORALean.Float


-- ========================================  `addDown`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

namespace IEEE

variable {fmt : IEEEFormat}

/-- `Dyadic.exactAdd`, which loses nothing, then `roundDown` onto the grid of `fmt`. -/
def addDown (a b : IEEE fmt) : IEEE fmt := roundDown (Dyadic.exactAdd a.toDyadic b.toDyadic)

end IEEE

end CORALean.Float


-- ========================================  `divDown`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

namespace IEEE

variable {fmt : IEEEFormat}

/-- `DivUp`'s mirror: `Dyadic.divDown` to `p` bits, then `roundDown` onto the grid. -/
def divDown (a b : IEEE fmt) : IEEE fmt := roundDown (Dyadic.divDown a.toDyadic b.toDyadic)

end IEEE

end CORALean.Float


-- ========================================  `mulDown`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

namespace IEEE

variable {fmt : IEEEFormat}

/-- `Dyadic.exactMul`, which loses nothing, then `roundDown` onto the grid of `fmt`. -/
def mulDown (a b : IEEE fmt) : IEEE fmt := roundDown (Dyadic.exactMul a.toDyadic b.toDyadic)

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
