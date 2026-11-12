module

public import CORALean.ContDynamics.LinearSys.Krylov.Definitions.LyapunovCertificateFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Operations.RestartedBetaFloat
public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# A bound of the error of restarted Krylov steps in a Lyapunov weight, in floats

[1, Sec. 7] with the growth of the exact steps measured in the weight `P` of an accepted
`Krylov.lyapunovCertificateFloat` instead of the 2-norm, where `‖e^{tA}‖₂` can be large for a stable
non-normal `A` although `e^{tA}` decays. The local 2-norm errors `ε'_j` of the windows (the bound
of `Krylov.errorBoundFloat` at the window's start vector) accumulate in the weight as
`β_{j+1} = e^{μΔt_j} β_j + √b ε'_j`, `β_0 = 0`, and the 2-norm error after `N` windows is at most
`β_N/√a`, `a = lower`, `b = upper`, `μ = rate`: the factor `√(b/a)` is paid once. Every operation is
rounded up; the exponential's argument must be within `expUp`'s range for every window.

## Inputs
* `p` – Newton steps per root
* `q` – squarings of the exponential
* `c` – accepted Lyapunov weight
* `Δt` – window lengths
* `ε` – local 2-norm errors of the windows
* `N` – number of windows

## Output
* upper bound of the 2-norm error after `N` windows, and whether it is certified

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

/-- `β_N/√a`, rounded up: `β_N` times the root of `1/a` rounded up. -/
def Krylov.restartedErrorBoundFloat (p q : ℕ) (c : Krylov.LyapunovCertificateFloat 𝕋)
    (Δt ε : ℕ → 𝕋) (N : ℕ) : 𝕋 :=
  -- `√b` and the accumulated bound `β_N`
  let root := sqrtUp p c.upper
  let β := Krylov.restartedBetaFloat q root c.rate Δt ε N
  -- `1/√a`
  mulUp β (sqrtUp p (divUp one c.lower))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
