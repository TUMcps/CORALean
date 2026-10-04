import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStripBased
import CORALean.ContDynamics.LinearSysDT.Theorems.Real.ObserveStepOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter

/-!
# The strip-based observer holds the true state

CORA's `observe_stripBased`, [1, Alg. 1] run over time: every run `x_{k+1} = A x_k + u_k + ω_k`
from `x_0 ∈ R₀` with `ω_k ∈ W`, whose outputs meet every strip `|C x_k - y_k| ≤ σ`, is in
the observer's set at every step, whatever the gains and the order. Induction on `k`:
`observeStep_outer` at the one state `x_k`, then `reduce_outer`.

[2, Eq. 4], over time: the strip-based observer encloses the true state.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
* [2] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Real

variable {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.observeStripBased_outer (sys : LinearSysDT ℝ n) (C : Mat ℝ p n)
    (σ : Vec ℝ p) (W R₀ : Zonotope (Vec ℝ n)) (u : ℕ → Vec ℝ n) (y : ℕ → Vec ℝ p)
    (options : LinearSysDT.ObserveStripOptions n p) (x w : ℕ → Vec ℝ n)
    (h0 : x 0 ∈ R₀.construct) (hw : ∀ k, w k ∈ W.construct)
    (hstep : ∀ k, x (k + 1) = sys.A *ᵥ x k + u k + w k)
    (hy : ∀ k i, |(C *ᵥ x k - y k) i| ≤ σ i) (k : ℕ) :
    x k ∈ (sys.observeStripBased C σ W R₀ u y options k).construct := by -- --- PROOF ---
  induction k with
  | zero =>
    unfold LinearSysDT.observeStripBased
    split
    · exact Zonotope.intersectStripSeq_outer _ _ _ _ _ ⟨h0, hy 0⟩
    · exact Zonotope.intersectStrip_outer _ _ _ _ _ ⟨h0, hy 0⟩
  | succ k ih =>
    unfold LinearSysDT.observeStripBased
    refine Zonotope.reduce_outer _ _ ?_
    refine sys.observeStep_outer C σ W options (u k) (y (k + 1)) _
      (Set.singleton_subset_iff.mpr ih) ⟨⟨_, ⟨x k, rfl, rfl⟩, w k, hw k, ?_⟩, hy (k + 1)⟩
    rw [hstep]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
