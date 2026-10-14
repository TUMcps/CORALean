module

public import CORALean.Global.Float.Instances.Dyadic.Theorems.Basic
public import CORALean.Global.Float.Instances.Dyadic.Theorems.DivDownLeDiv
public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeDivUp
public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeIff
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactAdd
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactMul
public import CORALean.Global.Float.Instances.IEEE.Operations.AddUp
public import CORALean.Global.Float.Instances.IEEE.Operations.Basic
public import CORALean.Global.Float.Instances.IEEE.Operations.DivUp
public import CORALean.Global.Float.Instances.IEEE.Operations.Half
public import CORALean.Global.Float.Instances.IEEE.Operations.MulUp
public import CORALean.Global.Float.Instances.IEEE.Theorems.LeRoundUp
public import CORALean.Global.Float.Instances.IEEE.Theorems.RoundDownLe

@[expose] public section

/-!
# `Global/Float/Instances/IEEE/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- ======================================  `add_le_addUp`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The exact sum is `Dyadic`'s, and `le_roundUp` rounds it up. -/
theorem add_le_addUp (a b : IEEE fmt) : a.toReal + b.toReal ≤ (addUp a b).toReal :=
  calc a.toReal + b.toReal = (Dyadic.exactAdd a.toDyadic b.toDyadic).toReal :=
        (Dyadic.toReal_exactAdd _ _).symm
    _ ≤ _ := le_roundUp _


-- =====================================  `addDown_le_add`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The exact sum is `Dyadic`'s, and `roundDown_le` rounds it down. -/
theorem addDown_le_add (a b : IEEE fmt) : (addDown a b).toReal ≤ a.toReal + b.toReal :=
  calc (addDown a b).toReal ≤ (Dyadic.exactAdd a.toDyadic b.toDyadic).toReal := roundDown_le _
    _ = a.toReal + b.toReal := Dyadic.toReal_exactAdd _ _


-- ======================================  `div_le_divUp`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Dyadic.le_divUp` for the first rounding, `le_roundUp` for the second. -/
theorem div_le_divUp (a b : IEEE fmt) (hb : 0 < b.toReal) :
    a.toReal / b.toReal ≤ (divUp a b).toReal :=
  le_trans (Dyadic.le_divUp a.toDyadic b.toDyadic hb) (le_roundUp _)


-- =====================================  `divDown_le_div`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Dyadic.divDown_le_div` for the first rounding, `roundDown_le` for the second. -/
theorem divDown_le_div (a b : IEEE fmt) (hb : 0 < b.toReal) :
    (divDown a b).toReal ≤ a.toReal / b.toReal :=
  le_trans (roundDown_le _) (Dyadic.divDown_le_div a.toDyadic b.toDyadic hb)


-- =========================================  `le_iff`  ========================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Both directions, read off `Dyadic.le_iff`. -/
theorem le_iff (a b : IEEE fmt) : le a b = true ↔ a.toReal ≤ b.toReal :=
  Dyadic.le_iff a.toDyadic b.toDyadic


-- ======================================  `mul_le_mulUp`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The exact product is `Dyadic`'s, and `le_roundUp` rounds it up. -/
theorem mul_le_mulUp (a b : IEEE fmt) : a.toReal * b.toReal ≤ (mulUp a b).toReal :=
  calc a.toReal * b.toReal = (Dyadic.exactMul a.toDyadic b.toDyadic).toReal :=
        (Dyadic.toReal_exactMul _ _).symm
    _ ≤ _ := le_roundUp _


-- =====================================  `mulDown_le_mul`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The exact product is `Dyadic`'s, and `roundDown_le` rounds it down. -/
theorem mulDown_le_mul (a b : IEEE fmt) : (mulDown a b).toReal ≤ a.toReal * b.toReal :=
  calc (mulDown a b).toReal ≤ (Dyadic.exactMul a.toDyadic b.toDyadic).toReal := roundDown_le _
    _ = a.toReal * b.toReal := Dyadic.toReal_exactMul _ _


-- ======================================  `toReal_half`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- It is `Dyadic.half` on the same pair, which is why it may leave the grid. -/
theorem toReal_half (x : IEEE fmt) : (half x).toReal = x.toReal / 2 :=
  Dyadic.toReal_half x.toDyadic


-- =======================================  `toReal_neg`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- It is `Dyadic.neg` on the same pair. -/
theorem toReal_neg (x : IEEE fmt) : (neg x).toReal = -x.toReal := Dyadic.toReal_neg x.toDyadic

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
