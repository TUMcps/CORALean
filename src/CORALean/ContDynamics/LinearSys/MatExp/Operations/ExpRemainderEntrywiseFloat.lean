module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureFloat
public import CORALean.ContSet.Interval.Float.Operations.MagnitudeMat
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# `MatExp.expRemainderEntrywise`, a float bound on the entrywise remainder `E(Δt,η)`

`Real.MatExp.expRemainderMat` rounded up, the `E(Δt,η)` of [1]: CORA takes `E(Δt,η) = e^{|A|Δt} −
Σ_{i≤η}(|A|Δt)ⁱ/i!` from MATLAB's `expm`, which no float guarantees. Here `e^{|A|Δt}` is enclosed
by `expIntervalEnclosure` of `[|A|Δt]` at the order `ηe + 8`, the series by `expIntervalTaylor` at
`η`; the entry is the enclosure's upper end less the series' lower end, rounded up. The scalar tail
is that of order `ηe + 8`, tiny, while the terms between `η` and `ηe + 8` enter entry by entry: an
entry whose true tail is zero is not given the tail past `ηe`. Needs `‖|A|Δt‖ ≤ (ηe + 2)/2`.

## Inputs
* `A` – system matrix
* `Δt` – step length
* `η` – Taylor order of the step
* `ηe` – Taylor order of the step's admissible enclosure; `e^{|A|Δt}` is enclosed at `ηe + 8`

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
-- Last update:   12-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `W ≥ E(Δt,η)` entrywise: the enclosure of `e^{|A|Δt}` at order `ηe + 8` less the series. -/
def MatExp.expRemainderEntrywise (A : Mat 𝕋 n n) (Δt : 𝕋) (η ηe : ℕ) : Mat 𝕋 n n :=
  let M := Interval.magnitudeMat (Interval.point A)                      -- `|A|`
  let B := Interval.smul Δt Δt (Interval.point M)                        -- `[|A|Δt]`
  let T := MatExp.expIntervalTaylor B η                                  -- series up to order `η`
  let X := MatExp.expIntervalEnclosure B (ηe + 8)                        -- encloses `e^{|A|Δt}`
  let w : Mat 𝕋 n n := fun j k => subUp (X.sup j k) (T.inf j k)          -- the entries
  let W : Interval (Mat 𝕋 n n) := ⟨w, w⟩
  W.materialiseMat.sup                                                   -- stored, read `n²` times

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
