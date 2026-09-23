import CORALean.ContSet.Zonotope.Real.Definitions.ReduceBoxAdmissible
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBoxOrder

/-!
# The chosen order is the least admissible one

What makes `reduceBoxOrder` a tuning rule rather than an arbitrary choice: no
admissible order is smaller, so the reduction is as coarse as the stated bound
allows.

Needs no hypothesis on `B`: an admissible `o` in hand is itself the witness
that the set is inhabited, so the empty-set branch of `sInf` cannot be the one
taken — the same shape `MatExp.expRemainderOrder_le` has.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Minimality: every order meeting `B` is at least the one chosen for it. -/
theorem Zonotope.reduceBoxOrder_le {Z : Zonotope (Vec ℝ n)} {B : Set (Vec ℝ n)} {o : ℕ}
    (h : Z.ReduceBoxAdmissible B o) : Z.reduceBoxOrder B ≤ o :=
  Nat.sInf_le h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
