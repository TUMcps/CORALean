module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.RestartedErrorOkFloat

@[expose] public section

/-!
# Whether the error bound inside a restart window is certified

The bound of `Krylov.windowErrorBoundFloat` ([1, Sec. 7] inside a window) counts no decay of the
accumulated error inside the window, which is a bound only for a weight whose rate is nonpositive.
It is certified when `Krylov.restartedErrorOkFloat` holds for the finished windows and `rate ≤ 0`.
(An accepted weight has a positive gap and upper bound, so its rate `-(gap/(2 upper))` is
nonpositive at every machine; the test is made because rounding down is not shown to keep a
quotient nonnegative.)

## Inputs
* `q` – squarings of the exponential
* `c` – Lyapunov weight
* `Δt` – lengths of the finished windows
* `N` – number of finished windows

## Output
* whether the bound is certified

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Krylov.restartedErrorOkFloat` and `rate ≤ 0`. -/
def Krylov.windowErrorOkFloat (q : ℕ) (c : Krylov.LyapunovCertificateFloat 𝕋) (Δt : ℕ → 𝕋)
    (N : ℕ) : Bool :=
  Krylov.restartedErrorOkFloat q c Δt N && le c.rate zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
