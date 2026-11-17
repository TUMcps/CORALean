module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# `LinearSys.verifyTimeDropCora`: the unverified times lose their short intervals

`aux_removeFromUnsat` in `@linearSys/private/priv_verifyRA_supportFunc.m` ends with
`idxRemove = abs(FGunsat(:,2) - FGunsat(:,1)) < 1e-14; FGunsat(idxRemove,:) = [];`
(ll. 1075-1076): every unverified interval shorter than `1e-14` is dropped, whatever the time
scale. Meant for the rounding remainders of the step times, it also drops a whole unverified step
once `Δt < 1e-14`, and the verdict `true` then covers times no pass verified. Modelled as printed,
with exact times.

# A step of `10⁻¹⁵` that no pass verified is dropped

`U = [[17·10⁻¹⁵, 18·10⁻¹⁵]]`, a step of a pass of `100` steps of `10⁻¹⁵` that was not verified:
the filter leaves no unverified time, while `17.5·10⁻¹⁵` was never verified. In MATLAB (R2024b,
CORA v2026.1.0) the rotation `ẋ = ω [0 -1; 1 0] x`, `ω = π / (35·10⁻¹⁵)`, from `(1, 0)` against
`x₂ ≤ 0.999` over `10⁻¹³` returns `res = 1` in one pass of `100` steps, although
`x₂(17.5·10⁻¹⁵) = 1`; at every time point `x₂ ≤ cos(π/70) < 0.999`, so nothing is falsified. The
same system with the time scaled by `10¹⁵` returns `res = 0`, falsified at `17.2`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's filter leaves no unverified interval, although a time of `U` lies in none
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- ll. 1075-1076: the unverified intervals without those shorter than `1e-14`. -/
def LinearSys.verifyTimeDropCora (U : List (ℚ × ℚ)) : List (ℚ × ℚ) :=
  U.filter fun iv => ¬(|iv.2 - iv.1| < 1 / 10 ^ 14)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The unverified step `[17·10⁻¹⁵, 18·10⁻¹⁵]` is dropped, though `17.5·10⁻¹⁵` lies in it. -/
theorem LinearSys.verifyTimeDropCora_counterexample :
    let U : List (ℚ × ℚ) := [(17 / 10 ^ 15, 18 / 10 ^ 15)]
    LinearSys.verifyTimeDropCora U = [] ∧ ∃ iv ∈ U, iv.1 < 35 / (2 * 10 ^ 15)
      ∧ 35 / (2 * 10 ^ 15) < iv.2 := by
  intro U
  refine ⟨?_, ⟨_, List.mem_cons_self, by norm_num, by norm_num⟩⟩
  simp only [LinearSys.verifyTimeDropCora, U, List.filter_cons, List.filter_nil]
  norm_num

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
