import CORALean.Global.Float.FloatOps

/-!
# A float bracket of the sample time `k Δt`

`t_k = k Δt` need not be a float, so a window encloses it by two: this doubles
the bracket of `t_{⌊k/2⌋}` and adds `Δt` once more when `k` is odd, rounding
down on one side and up on the other. `O(log k)` additions, each sound at any
sign of `Δt` — `addDown`/`addUp` bound a sum whatever its terms — and each
window's bracket computed from `k` alone, independent of every other window.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(lo, hi)` with `lo ≤ k Δt ≤ hi`, by binary doubling. -/
def LinearSys.sampleTimeFloat (Δt : 𝕋) : ℕ → 𝕋 × 𝕋
  | 0 => (zero, zero)
  | k + 1 =>
    let h := LinearSys.sampleTimeFloat Δt ((k + 1) / 2)             -- t_{⌊k/2⌋}, bracketed
    let d := (addDown h.1 h.1, addUp h.2 h.2)                       -- doubled
    if (k + 1) % 2 = 0 then d else (addDown d.1 Δt, addUp d.2 Δt)   -- and Δt once more if odd
termination_by k => k
decreasing_by omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
