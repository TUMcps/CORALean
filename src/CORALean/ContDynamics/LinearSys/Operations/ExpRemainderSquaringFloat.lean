module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpSquaringFloat
public import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# `LinearSys.expRemainderSquaringFloat`, CORA's remainder `E(Δt,η)` by scaling and squaring

CORA's `priv_expmRemainder` takes `E(Δt,η) = e^{|A|Δt} − Σ_{i≤η}(|A|Δt)ⁱ/i!` from MATLAB's `expm`,
which no float guarantees. Here `e^{|A|Δt}` is enclosed as `expSquaringFloat` encloses `e^{AΔt}`:
the order-`16` enclosure at `|A|Δt / 2^s`, squared `s` times. The series is `expIntervalTaylor` at
`η`; an entry is the enclosure's upper end less the series' lower end, rounded up. The order of the
step stays `η`: the squarings, not a raised order, keep the enclosure tight for a stiff `A`.

## Inputs
* `sys` – linear system
* `Δt` – step length
* `η` – Taylor order of the step
* `s` – halvings of `|A|Δt` before the enclosure (`halvingsFloat` of `|A|`)

## Output
* float matrix bounding the entrywise remainder from above
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

/-- `W ≥ E(Δt,η)` entrywise: `e^{|A|Δt}` by scaling and squaring, less the series up to `η`. -/
def LinearSys.expRemainderSquaringFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η s : ℕ) :
    Mat 𝕋 n n :=
  let M := Interval.magnitudeMat (Interval.point sys.A)                  -- `|A|`
  let B := Interval.smul Δt Δt (Interval.point M)                        -- `[|A|Δt]`
  let T := MatExp.expIntervalTaylor B η                                  -- series up to order `η`
  let sysM : LinearSys 𝕋 n := { sys with A := M }                        -- the system of `|A|`
  let X := sysM.expSquaringFloat Δt Δt 16 s                              -- encloses `e^{|A|Δt}`
  let w : Mat 𝕋 n n := fun j k => subUp (X.sup j k) (T.inf j k)          -- the entries
  let W : Interval (Mat 𝕋 n n) := ⟨w, w⟩
  W.materialiseMat.sup                                                   -- stored, read `n²` times

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
