module

public import CORALean.Global.Float.FloatOps
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# A float bracket of the sample time `k Δt`

`t_k = k Δt` need not be a float, so a window encloses it by an interval: this doubles
the bracket of `t_{⌊k/2⌋}` and adds `Δt` once more when `k` is odd, rounding
down on one side and up on the other. `O(log k)` additions, each sound at any
sign of `Δt` — `addDown`/`addUp` bound a sum whatever its terms — and each
window's bracket computed from `k` alone, independent of every other window.

## Inputs
* `Δt` – float step length

## Output
* float interval bracketing the sample time of a given index
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The interval `[lo, hi]` with `lo ≤ k Δt ≤ hi`, by binary doubling. -/
def LinearSys.sampleTimeFloat (Δt : 𝕋) : ℕ → Interval 𝕋
  | 0 => ⟨zero, zero⟩
  | k + 1 =>
    let h := LinearSys.sampleTimeFloat Δt ((k + 1) / 2)             -- t_{⌊k/2⌋}, bracketed
    let d : Interval 𝕋 := ⟨addDown h.inf h.inf, addUp h.sup h.sup⟩  -- doubled
    if (k + 1) % 2 = 0 then d else ⟨addDown d.inf Δt, addUp d.sup Δt⟩ -- and Δt once more if odd
termination_by k => k
decreasing_by omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
