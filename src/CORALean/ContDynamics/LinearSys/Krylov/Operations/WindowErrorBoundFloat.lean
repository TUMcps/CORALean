module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.RestartedBetaFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Definitions.LyapunovCertificateFloat
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# A bound of the error at every time inside a restart window, in floats

[1, Sec. 7] inside window `N`: the accumulated error `β_N` of the finished windows in the weight of
an accepted `Krylov.lyapunovCertificateFloat` (`Krylov.restartedBetaFloat`) is not decayed, as the
weight's rate is nonpositive, and the local 2-norm error `ε'_N` of the window (the bound at its end,
which the local bound does not exceed earlier) enters through `√b`: at every time of the window the
2-norm error is at most `(β_N + √b ε'_N)/√a`, `a = lower`, `b = upper`. This is CORA.cpp's
`RestartedBound::window_bound`; `Krylov.restartedErrorBoundFloat` is the same at the window's end
after the decay. Every operation is rounded up.

## Inputs
* `p` – Newton steps per root
* `q` – squarings of the exponential
* `c` – accepted Lyapunov weight
* `Δt` – lengths of the finished windows
* `ε` – local 2-norm errors of the windows, `ε N` that of the window in question
* `N` – number of finished windows

## Output
* upper bound of the 2-norm error at every time of window `N`

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

/-- `(β_N + √b ε'_N)/√a`, rounded up: the sum, then the root of `1/a` rounded up. -/
def Krylov.windowErrorBoundFloat (p q : ℕ) (c : Krylov.LyapunovCertificateFloat 𝕋)
    (Δt ε : ℕ → 𝕋) (N : ℕ) : 𝕋 :=
  -- `√b` and the accumulated bound `β_N` of the finished windows
  let root := sqrtUp p c.upper
  let β := Krylov.restartedBetaFloat q root c.rate Δt ε N
  -- `β_N + √b ε'_N`, then `1/√a`
  mulUp (addUp β (mulUp root (ε N))) (sqrtUp p (divUp one c.lower))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
