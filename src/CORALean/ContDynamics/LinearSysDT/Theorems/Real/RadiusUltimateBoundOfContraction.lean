module

public import CORALean.Global.UltimateBoundOfRecurrence
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Topology.Algebra.Algebra

@[expose] public section

/-!
# The ultimate bound of the P-radius of the corrected zonotopes

The last clause of [1, Thm. 1]: if the P-radii contract, `V(X(k)) ≤ γ V(X(k-1)) + ε` Eq. 15 of
[1, Thm. 1] with `γ ∈ (0, 1)`, then `V(X(∞)) ≤ ε / (1 - γ)`. The paper writes `V(X(∞))` for the
radius at `k → ∞`, which exists only if the radii converge. So the bound is proved for the limit
where there is one, `L ≤ γ L + ε`, and, without that assumption, for every `k`,
`V(X(k)) ≤ γᵏ V(X(0)) + ε / (1 - γ)`, which is eventually below `ε / (1 - γ) + δ` for every `δ >
0`: the bound for the limit superior. The step `V(X(k)) ≤ γ V(X(k-1)) + ε` is
`Zonotope.correctedStep_pRadius_le`. `0 ≤ γ < 1` and `ε ≥ 0` are used.

## Inputs
* `V` – radius sequence
* `γ` – contraction factor
* `ε` – disturbance level

## Hypotheses
* `hγ0` – contraction factor nonnegative
* `hγ1` – contraction factor below one
* `hε` – disturbance level nonnegative
* `h15` – radii contract

## Conclusion
* the radii are bounded by a geometric term plus the ultimate bound

## References

* [1] [Y. Wang, T. Alamo, V. Puig and G. Cembrano. "A distributed set-membership approach based on
      zonotopes for interconnected systems". 2018 IEEE Conference on Decision and Control (CDC),
      2018.](../../../../../../references/2018/wang-cdc-distributed-set-membership.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.radius_ultimate_bound (V : ℕ → ℝ) (γ ε : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 ≤ ε) (h15 : ∀ k, V (k + 1) ≤ γ * V k + ε) : -- --- CONCL ---
    (∀ k, V k ≤ γ ^ k * V 0 + ε / (1 - γ)) ∧
      (∀ δ > 0, ∀ᶠ k in atTop, V k ≤ ε / (1 - γ) + δ) ∧
      ∀ L, Tendsto V atTop (nhds L) → L ≤ ε / (1 - γ) := by -- --- PROOF ---
  obtain ⟨h1, h2⟩ := ultimately_le_of_le_mul_add V γ ε hγ0 hγ1 hε h15
  refine ⟨h1, h2, fun L hL => ?_⟩
  have hL' : Tendsto (fun k => V (k + 1)) atTop (nhds L) := hL.comp (tendsto_add_atTop_nat 1)
  have hle : L ≤ γ * L + ε :=
    le_of_tendsto_of_tendsto' hL' ((hL.const_mul γ).add_const ε) h15
  have hpos : 0 < 1 - γ := by linarith
  rw [le_div_iff₀ hpos]
  nlinarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
