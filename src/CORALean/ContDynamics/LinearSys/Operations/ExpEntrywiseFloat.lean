module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorFloat
public import CORALean.ContDynamics.LinearSys.LinearSys

@[expose] public section

/-!
# `LinearSys.expEntrywiseFloat`, `e^{AΔt}` as the series and its entrywise remainder

`[e^{AΔt}]` for CORA's closed form [1]: the Taylor series of `AΔt` up to order `η` by
`expIntervalTaylor` at the point matrix `A`, widened by `[-W, W]`, the entry's own bound of
`expRemainderEntrywise`.
`expIntervalFloat` widens by one scalar bound instead.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order
* `W` – float bound on the entrywise remainder

## Output
* float interval matrix enclosing the exponential at the step

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[e^{AΔt}]`: the series up to `η`, widened by `[-W, W]`. -/
def LinearSys.expEntrywiseFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) (W : Mat 𝕋 n n) :
    Interval (Mat 𝕋 n n) :=
  let T := MatExp.expIntervalTaylor (Interval.smul Δt Δt (Interval.point sys.A)) η  -- series
  (⟨fun j k => subDown (T.inf j k) (W j k), fun j k => addUp (T.sup j k) (W j k)⟩ :
    Interval (Mat 𝕋 n n)).materialiseMat

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
