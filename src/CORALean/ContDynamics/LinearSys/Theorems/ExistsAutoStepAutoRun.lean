module

public import CORALean.ContDynamics.LinearSys.Theorems.AutoRunBudget
public import CORALean.ContDynamics.LinearSys.Theorems.ExistsAutoStep

@[expose] public section

/-!
# `Thm. 1` along the whole run: every iteration of `Alg. 2` inside the horizon completes

`exists_autoStep` carries two budget invariants (`ε^a_k` and `ε^r_k` inside eq. (36)'s and eq.
(35)'s shares at `t_k`) and `exists_autoStep_autoInit` discharges them at `k = 0` only.
`autoRun_budget` discharges them at every `k`, so nothing is carried here either: whatever state a
run of [1, Alg. 2] has reached, the `while` of line 4 still holding, some fuel lets the next
iteration report. Two readings of the caller's `le` are wanted: the sweeps must be *complete* for a
candidate to be found at all, and *sound* for the candidate found to have met its share. Termination
is still not claimed; see the `Thm. 1` row and finding on the reference page.

## Inputs
* `sys` – linear system
* `le` – comparison oracle on reals
* `X₀` – initial zonotope
* `U` – input zonotope
* `tend` – final time
* `εmax` – admissible error
* `ζ` – error budget share
* `ηmax` – maximal Taylor order
* `fuel` – number of shrinkings
* `k` – iteration count

## Hypotheses
* `hle` – comparison oracle is complete
* `hle'` – comparison oracle is sound
* `hn` – dimension positive
* `htpos` – final time positive
* `hεmax` – admissible error positive
* `hζ0` – error share nonnegative
* `hζ1` – error share below one
* `hηmax` – maximal order at least one

## Conclusion
* from any reached state before the horizon some fuel makes the next iteration report

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1] at every `k`: from any state a run of `Alg. 2` has reached before the
horizon, some fuel lets the next iteration report rather than give out. -/
theorem LinearSys.exists_autoStep_autoRun (sys : LinearSys 𝕋 n) {le : ℝ → ℝ → Bool}
    (hle : ∀ a b : ℝ, a ≤ b → le a b = true) (hle' : ∀ a b : ℝ, le a b = true → a ≤ b)
    (X₀ U : Zonotope (Vec ℝ n)) {tend εmax ζ : ℝ} {ηmax fuel k : ℕ} (hn : 0 < n) (htpos : 0 < tend)
    (hεmax : 0 < εmax) (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) (hηmax : 1 ≤ ηmax) : -- --- CONCL ---
    ∀ s ∈ sys.autoRun le X₀ U tend εmax ζ ηmax fuel k,
      s.t < tend →
      ∃ (fuel' : ℕ) (r : LinearSys.AutoState n × Zonotope (Vec ℝ n)),
        sys.autoStep le X₀ U tend εmax ζ ηmax fuel' s = some r := by -- --- PROOF ---
  intro s (hrun : sys.autoRun le X₀ U tend εmax ζ ηmax fuel k = some s) hlt
  obtain ⟨-, hΔt, hεa, hεr⟩ := sys.autoRun_budget hle' X₀ U htpos ηmax fuel k s hrun
  exact sys.exists_autoStep hle X₀ U s hn hlt htpos hεmax hζ0 hζ1 hεa hεr hΔt hηmax

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
