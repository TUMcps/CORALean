module

public import CORALean.Specification.Rtl.Definitions.IsHalfMultiple
public import CORALean.Specification.Rtl.Rtl

@[expose] public section

/-!
# `Rtl/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").

Real-only, a specification: it builds RTL formulas, whose time constants are syntax rather than
computed values.
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {L : Type}


-- ========================================  `Rtl.and?`  ======================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `res = and(obj1,obj2)`: an empty operand (`none`) gives the other. -/
def Rtl.and? : Option (Rtl L) → Option (Rtl L) → Option (Rtl L)
  | none, o2 => o2
  | o1, none => o1
  | some a, some b => some (.and a b)


-- =======================================  `Rtl.next?`  ======================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

open Classical in
/-- `res = next(obj,time)`: CORA throws unless `time` is a multiple of `0.5`; here `none`. -/
noncomputable def Rtl.next? (obj : Rtl L) (time : ℝ) : Option (Rtl L) :=
  if Rtl.IsHalfMultiple time then some (.next time obj) else none


-- ========================================  `Rtl.or?`  ========================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `res = or(obj1,obj2)`: an empty operand (`none`) gives the other. -/
def Rtl.or? : Option (Rtl L) → Option (Rtl L) → Option (Rtl L)
  | none, o2 => o2
  | o1, none => o1
  | some a, some b => some (.or a b)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
