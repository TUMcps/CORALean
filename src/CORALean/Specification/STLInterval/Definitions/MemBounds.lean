module

public import CORALean.Specification.STLInterval.STLInterval
public import Mathlib.Order.WithBot

@[expose] public section

/-!
# The times between real bounds

The times `t` with `lb < t` (or `lb = t` when `lc`) and `t < ub` (or `t = ub` when `rc`), for real
bounds and an upper bound that may be `inf` (`⊤`): the denotation of `stlInterval(lb,ub,lc,rc)` that
the signals use, as `STLInterval.set` for bounds of type `EReal`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `contains(stlInterval(lb,ub,lc,rc),t)`. -/
def STLInterval.memBounds {T : Type} [LinearOrder T] (lb : T) (ub : WithTop T) (lc rc : Bool)
    (t : T) : Prop :=
  (lb < t ∨ (lc = true ∧ t = lb)) ∧ ((t : WithTop T) < ub ∨ (rc = true ∧ (t : WithTop T) = ub))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
