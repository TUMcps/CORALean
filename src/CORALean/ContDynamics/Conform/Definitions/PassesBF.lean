module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContDynamics.Conform.Definitions.Conformant

@[expose] public section

/-!
# The brute-force conformance check

`priv_isconform_BF` of `contDynamics/isconform` [1]: for every test case the reachable set of the
system is computed, started from the recorded initial state, and every measurement up to the
horizon must lie in the set of its step. `R m k` is the set `reach` computed for test case `m` at
step `k`, after the order reduction CORA applies; it is a parameter, so the check is stated for
whatever set-based `reach` supplies. The verdict is `res`; the first measurement outside makes
CORA return `false` at once.

## Inputs
* `T` – test cases
* `K` – horizon
* `R` – computed reachable sets per test case and step

## Output
* every measurement up to the horizon lies in its reachable set

## References

* [1] `contDynamics/@contDynamics/private/priv_isconform_BF.m`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n p q : ℕ} {M S : Type} [ContSet S (Vec ℝ q)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every measurement up to `K` of every test case lies in the computed reachable set. -/
def Conform.PassesBF (T : M → Conform.TestCase n p q) (K : ℕ) (R : M → ℕ → S) : Prop :=
  ∀ m, ∀ k ≤ K, (T m).y k ∈ construct (R m k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
