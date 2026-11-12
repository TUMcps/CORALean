module

public import CORALean.ContDynamics.LinearSys.Krylov.Definitions.LyapunovCertificateFloat
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# Whether the restarted Krylov error bound in a Lyapunov weight is certified

The bound of `Krylov.restartedErrorBoundFloat` ([1, Sec. 7] accumulated in a Lyapunov weight) is a
bound only when the weight was accepted, a squaring is made and, for every window, the length is
nonnegative and the exponential's argument `Δt_j μ` is within `expUp`'s range (at most `2^{q-1}`).

## Inputs
* `q` – squarings of the exponential
* `c` – Lyapunov weight
* `Δt` – window lengths
* `N` – number of windows

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

/-- Whether the weight was accepted, there is a squaring and every window has `Δt_j ≥ 0` and
`Δt_j μ` within `expUp`'s range. -/
def Krylov.restartedErrorOkFloat (q : ℕ) (c : Krylov.LyapunovCertificateFloat 𝕋) (Δt : ℕ → 𝕋)
    (N : ℕ) : Bool :=
  c.ok && decide (1 ≤ q) && (List.range N).all fun j =>
    le zero (Δt j) && le (mulUp c.rate (Δt j)) (nsmulDown (2 ^ (q - 1)) one)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
