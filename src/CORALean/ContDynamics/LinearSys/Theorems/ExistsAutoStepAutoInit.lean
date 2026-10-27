module

public import CORALean.ContDynamics.LinearSys.Operations.AutoInit
public import CORALean.ContDynamics.LinearSys.Theorems.ExistsAutoStep

@[expose] public section

/-!
# `Thm. 1` with nothing carried: the first iteration of `Alg. 2` always completes

`exists_autoStep` carries two budget invariants — `ε^a_k` and `ε^r_k` inside eq. (36)'s
and eq. (35)'s shares at `t_k` — which [1] maintains across the loop rather than proves.
At `k = 0` there is nothing to carry: lines 1-2 set `t_0 ← 0` and both accumulated errors
to `0`, and `0 ≤ 0`. So the first iteration of [1, Alg. 2] completes for every `ε_max > 0`
outright, on the algorithm's own initial state and no assumption about it.

Line 1's `Δt_{-1} ← t_end` is also what makes the halving sweep start from a positive
step, so `0 < t_end` does the work of two hypotheses here.

## Inputs
* `sys` – linear system
* `le` – comparison oracle on reals
* `X₀` – initial zonotope
* `U` – input zonotope
* `tend` – final time
* `εmax` – admissible error
* `ζ` – error budget share
* `ηmax` – maximal Taylor order

## Hypotheses
* `hle` – comparison oracle is complete
* `hn` – dimension positive
* `htpos` – final time positive
* `hεmax` – admissible error positive
* `hζ0` – error share nonnegative
* `hζ1` – error share below one
* `hηmax` – maximal order at least one

## Conclusion
* some fuel makes the first iteration report a step

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
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

/-- [1, Thm. 1] at `k = 0`, with no invariant carried: for every `ε_max > 0` some fuel
lets the first iteration of `Alg. 2` report, from the state lines 1-2 build. -/
theorem LinearSys.exists_autoStep_autoInit (sys : LinearSys 𝕋 n) {le : ℝ → ℝ → Bool}
    (hle : ∀ a b : ℝ, a ≤ b → le a b = true) (X₀ U : Zonotope (Vec ℝ n))
    {tend εmax ζ : ℝ} {ηmax : ℕ} (hn : 0 < n) (htpos : 0 < tend) (hεmax : 0 < εmax)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) (hηmax : 1 ≤ ηmax) :
    ∃ (fuel : ℕ) (r : LinearSys.AutoState n × Zonotope (Vec ℝ n)),
      sys.autoStep le X₀ U tend εmax ζ ηmax fuel (LinearSys.autoInit X₀ tend)
        = some r :=
  sys.exists_autoStep hle X₀ U (LinearSys.autoInit X₀ tend) hn htpos htpos hεmax hζ0 hζ1
    (by simp [LinearSys.autoInit]) (by simp [LinearSys.autoInit]) htpos hηmax

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
