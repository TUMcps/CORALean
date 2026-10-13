module

public import CORALean.ContDynamics.Conform.Definitions.IntervalNorm
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A non-negative stretch comes out of the interval norm

`σ^T |G diag(α)| 1 = ∑ⱼ (σ^T |gⱼ|) αⱼ` for `α ≥ 0`: the interval norm of a stretched template is
linear in the stretch factors — what makes every cost here the objective of a linear
program ([2, Thm. 1], [3, Lemma 2]). [1, Def. 2] is the case `σ = 1`.

## References

* [1] S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems:
      Unifying Formal Controller Synthesis and Reachset-Conformant Identification". IEEE
      Transactions on Robotics, 39(5):3776-3790, 2023.
* [2] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
* [3] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem Conform.intervalNorm_smul {m : ℕ} {ι : Type} [Fintype ι] (σ : Vec ℝ m)
    (G : ι → Vec ℝ m) (α : ι → ℝ) (hα : ∀ j, 0 ≤ α j) :
    Conform.intervalNorm σ (fun j => α j • G j)
      = ∑ j, (∑ a, σ a * |G j a|) * α j := by -- --- PROOF ---
  unfold Conform.intervalNorm
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (hα j)]
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
