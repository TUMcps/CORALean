module

public import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpRemainderSquaringFloat
public import CORALean.ContDynamics.LinearSys.Operations.HalvingsFloat

@[expose] public section

/-!
# `MatExp.exponentialRemainder`, over a floating-point scalar

CORA's `@intervalMatrix/exponentialRemainder`: `E = [-W, W]` with `W = e^M - Σ_{i ≤ η} Mⁱ/i!` at
`M = abs(intMat)`. CORA takes `e^M` from MATLAB's `expm`, which no float guarantees; here `W` is
`expRemainderSquaringFloat` of `M` at the step `1`, `e^M` enclosed by scaling and squaring
(`halvingsFloat` halvings of `M` before the order-`16` enclosure) less the series' lower end,
rounded up. `none` where no count below `128` halves `M` to norm `1/2`; CORA returns `Inf` where
`expm` is not a number.

## Inputs
* `A` – float interval matrix
* `η` – Taylor order

## Output
* float interval matrix that holds the Taylor remainder of every member, or none
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[-W, W]` with `W ≥ e^M - Σ_{i ≤ η} Mⁱ/i!` entrywise, `M = abs(intMat)`. -/
def MatExp.exponentialRemainder (A : Interval (Mat 𝕋 n n)) (η : ℕ) :
    Option (Interval (Mat 𝕋 n n)) := do
  let M := Interval.magnitudeMat A                                        -- `abs(intMat)`
  let sys := LinearSys.canonicalFloat M                                   -- the system of `M`
  let sysM : LinearSys 𝕋 n := { sys with A := Interval.magnitudeMat (Interval.point sys.A) }
  let s ← sysM.halvingsFloat one                                          -- halvings of `M`
  let W := sys.expRemainderSquaringFloat one η s                          -- `e^M - Σ Mⁱ/i!`
  pure ⟨-W, W⟩                                        -- `[-W, W]`

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
