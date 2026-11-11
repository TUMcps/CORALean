module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureFloat
public import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# `MatExp.expRemainderEntrywise`, a float bound on the entrywise remainder `E(Δt,η)`

`Real.MatExp.expRemainderMat` rounded up, the `E(Δt,η)` of [1]: CORA computes `E(Δt,η) =
e^{|A|Δt} − Σ_{i≤η}(|A|Δt)ⁱ/i!` as the absolute value of MATLAB's `expm(|A|Δt)` minus the series,
and no float guarantees that `expm`. Here `e^{|A|Δt}` is enclosed by `expIntervalEnclosure` of the
box `[|A|Δt]` at the order `ηe`, the series by `expIntervalTaylor` at `η`, and the entry is the
rounded-up difference of the enclosure's upper end and the series' lower end. The enclosure needs
`‖|A|Δt‖ ≤ (ηe + 2)/2`.

## Inputs
* `A` – system matrix
* `Δt` – step length
* `η` – Taylor order of the step
* `ηe` – Taylor order of the enclosure of `e^{|A|Δt}`

## Output
* float matrix bounding the entrywise remainder from above

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

/-- `W ≥ E(Δt,η)` entrywise: the enclosure of `e^{|A|Δt}` less the series, rounded up. -/
def MatExp.expRemainderEntrywise (A : Mat 𝕋 n n) (Δt : 𝕋) (η ηe : ℕ) : Mat 𝕋 n n :=
  let M := Interval.magnitudeMat (Interval.point A)                      -- `|A|`
  let B := Interval.smul Δt Δt (Interval.point M)                        -- `[|A|Δt]`
  let T := MatExp.expIntervalTaylor B η                                  -- series up to order `η`
  let X := MatExp.expIntervalEnclosure B ηe                              -- encloses `e^{|A|Δt}`
  fun j k => subUp (X.sup j k) (T.inf j k)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
