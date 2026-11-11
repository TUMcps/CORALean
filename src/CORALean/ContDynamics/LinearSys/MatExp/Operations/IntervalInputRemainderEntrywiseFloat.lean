module

public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `MatExp.intervalInputRemainderEntrywise`, the input remainder `E(Δt,η)·Δt` in floats

`Real.MatExp.inputRemainderEntrywise` in floats, the remainder of [1]: `[-rW, rW]` with
the entry's own bound `W` of `expRemainderEntrywise` where `intervalInputRemainder` has one width
for every entry.

## Inputs
* `r` – float step length
* `W` – float bound on the entrywise remainder

## Output
* float interval matrix of the scaled remainder

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[-r W, r W]`, entry by entry, for a nonnegative `r`. -/
def MatExp.intervalInputRemainderEntrywise (r : 𝕋) (W : Mat 𝕋 n n) : Interval (Mat 𝕋 n n) :=
  ⟨fun j k => neg (mulUp r (W j k)), fun j k => mulUp r (W j k)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
