module

public import CORALean.ContDynamics.Conform.Definitions.IntervalNorm
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# [1, Eq. 11]: the interval norm's four properties

Sec. 3.1 lists, for `‖⟨c, G⟩‖_{Ĩ,σ} = σ^T |[c, G]| 1` with `σ > 0`: a) it is
non-negative, b) it vanishes at `⟨0⟩`, c) it is absolutely homogeneous, d) it is
subadditive under adding the matrices `[c, G]`. All four are properties of `σ^T |M| 1` as
a function of the matrix `M`, so they are stated here for any generator family — `[c, G]`
being the family with the center as one more column, and `intervalNorm` itself, [1,
Eq. 11]'s `‖·‖_{I,σ}`, the family without it. Only `σ ≥ 0` is used. Property d) prints
its first right-hand term as `‖⟨[c, G₁]⟩‖`, the `c` there being `c₁`.

## References

* [1] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 11]: a)-d) for `σ^T |M| 1`, `σ ≥ 0`. -/
theorem Conform.intervalNorm_props {m : ℕ} {ι : Type} [Fintype ι] (σ : Vec ℝ m)
    (hσ : ∀ a, 0 ≤ σ a) (G G₁ G₂ : ι → Vec ℝ m) (γ : ℝ) :
    0 ≤ Conform.intervalNorm σ G ∧ Conform.intervalNorm σ (0 : ι → Vec ℝ m) = 0 ∧
      Conform.intervalNorm σ (γ • G) = |γ| * Conform.intervalNorm σ G ∧
      Conform.intervalNorm σ (G₁ + G₂)
        ≤ Conform.intervalNorm σ G₁ + Conform.intervalNorm σ G₂ := by -- --- PROOF ---
  unfold Conform.intervalNorm
  refine ⟨Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun a _ =>
    mul_nonneg (hσ a) (abs_nonneg _), by simp, ?_, ?_⟩
  · -- c): `|γ g| = |γ| |g|`
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    ring
  · -- d): the triangle inequality entrywise, weighted by `σ ≥ 0`
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (hσ a)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
