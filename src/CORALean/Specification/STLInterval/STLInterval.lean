module

public import CORALean.Global.Float.Instances.Real.Theorems.Basic
public import CORALean.Specification.STLInterval.Definitions.ToEReal

@[expose] public section

/-!
# CORA's `stlInterval`: time intervals with open and closed ends

`specification/@stlInterval/stlInterval.m`: a time interval with open or closed ends, or the empty
one. `STLInterval.nonempty` carries what `stlInterval(lb,ub,lc,rc)` establishes (an infinite bound
is open, `lb > ub` or `lb = ub` with an open end is empty, `lb ≥ 0`); `set` is the times denoted.
The bounds are stored in the scalar `𝕋` of a layer: the lower one finite, the upper one possibly
`inf` (`WithTop 𝕋`), read as reals through `toReal` and `toEReal`. CORA throws on `lb < 0`, so
`zero_le` is a field. `rawSet` is the times between any two extended-real bounds, as operations
compute bounds outside `[0, ∞]` before clamping (`rawSet_add`, `rawSet_sub`, `rawSet_clamp`). The
intervals are those of [1, Sec. 2.1 (intervals)].

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   23-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- A time interval with open or closed ends, or the empty one; a nonempty one has a lower bound of
at least zero and its lower bound below its upper, or equal with both ends closed. -/
inductive STLInterval (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  | empty
  | nonempty (lower : 𝕋) (upper : WithTop 𝕋) (leftClosed rightClosed : Bool)
      (upper_open : upper = ⊤ → rightClosed = false)
      (lt_or_point : ((toReal lower : ℝ) : EReal) < STLInterval.toEReal upper ∨
        (((toReal lower : ℝ) : EReal) = STLInterval.toEReal upper ∧ leftClosed = true ∧
          rightClosed = true))
      (zero_le : 0 ≤ toReal lower)

/-- The times between the bounds `l` and `u`, each end in when its flag is set; any pair of bounds,
not only those of an `stlInterval` (see the module docstring). -/
def STLInterval.rawSet (l u : EReal) (lc rc : Bool) : Set ℝ :=
  {t | (l < t ∨ (lc = true ∧ l = t)) ∧ ((t : EReal) < u ∨ (rc = true ∧ (t : EReal) = u))}

/-- The times an `stlInterval` denotes. -/
def STLInterval.set : STLInterval 𝕋 → Set ℝ
  | .empty => ∅
  | .nonempty l u lc rc _ _ _ => STLInterval.rawSet (toReal l : ℝ) (STLInterval.toEReal u) lc rc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
