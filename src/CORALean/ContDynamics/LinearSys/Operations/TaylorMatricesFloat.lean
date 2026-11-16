module

public import CORALean.ContDynamics.LinearSys.Definitions.TaylorMatrices
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrixTightFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixTightFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpRemainderSquaringFloat
public import CORALean.ContDynamics.LinearSys.Operations.HalvingsFloat

@[expose] public section

/-!
# `LinearSys.taylorMatricesFloat`, CORA's `taylorMatrices` over floats

CORA's `taylorMatrices` [1]: the remainder `E(Δt,η)` of `priv_expmRemainder`, then `F` of
`priv_correctionMatrixState` and `G` of `priv_correctionMatrixInput`, all at the order `η` of the
step. CORA's `E` is `expm(|A|Δt)` less the series, which no float guarantees; here it is
`expRemainderSquaringFloat`, the exponential of `|A|Δt` enclosed by scaling and squaring with the
halvings `halvingsFloat` gives for `|A|`. `F` and `G` are the entrywise correction matrices with
that bound and CORA's coefficient (`corrCoeffLowTight`). `none` if no count of halvings below
`128` brings `‖|A|Δt‖ / 2^s` to `1/2`.

## Inputs
* `sys` – linear system
* `Δt` – step length
* `η` – Taylor order

## Output
* the remainder bound `W`, `[F]` and `[G]`, none if the exponential cannot be enclosed

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[E, F, G] = taylorMatrices(sys, Δt, η)`, `E` enclosed by squaring; none past `128` halvings. -/
def LinearSys.taylorMatricesFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) :
    Option (LinearSys.TaylorMatrices 𝕋 n) := do
  let A := Interval.point sys.A                                           -- [A, A]
  let sysM : LinearSys 𝕋 n := { sys with A := Interval.magnitudeMat A }  -- the system of `|A|`
  let s ← sysM.halvingsFloat Δt                                           -- halvings of `|A|Δt`
  let W := sys.expRemainderSquaringFloat Δt η s                           -- `E(Δt,η)`
  let F := MatExp.intervalCorrectionMatrixTight A Δt η W                   -- state correction
  let G := MatExp.intervalConstCorrectionMatrixTight A Δt η W              -- input correction
  pure ⟨W, F, G⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
