module

public import CORALean.ContSet.Zonotope.Real.Theorems.CorrectedStepDistributedOuter

@[expose] public section

/-!
# The distributed set-membership estimator encloses every agent's state

The online procedure of [1, Sec. IV-C]: every agent `i` corrects its zonotope by [1, Prop. 1] from
its neighbours' zonotopes of the step before, `X_i(k) = red_i(⟨c_i(k), H_i(k)⟩)`, with its own
correction matrix `Λ_i`, and reduces the order by an over-bounding zonotope, [1, Lemma 1]'s
parallelotope or any other: `red_i Z ⊇ Z`. Then `x_i(k) ∈ X_i(k)` at every step `k`, if it holds at
`k = 0`. By induction: the correction step is `Zonotope.correctedStepDistributed_outer` and the
reduction only enlarges. The offline step, the correction matrices from [1, Eq. 23], is any
choice: every matrix is covered.

## Inputs
* `nb` – neighbour indices of each agent
* `A` – neighbour state matrices
* `B` – input matrices
* `Dw` – disturbance generator matrices
* `C` – output matrices
* `Dv` – noise generator matrices
* `Λ` – correction matrices
* `red` – order reductions
* `X` – state zonotope of each agent per step
* `u` – inputs per step
* `y` – measurements per step
* `x` – state trajectories
* `ϖ` – disturbance coefficients per step
* `σ` – noise coefficients per step

## Hypotheses
* `hred` – each reduction encloses its input
* `hX` – zonotopes follow the corrected step
* `hϖ` – disturbance coefficients within the unit box
* `hσ` – noise coefficients within the unit box
* `hx` – states follow the dynamics
* `hy` – measurements consistent with the states
* `h0` – initial states lie in the initial zonotopes

## Conclusion
* each agent's state lies in its zonotope at every step

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

namespace CORALean.Real

open Matrix

variable {ι : Type} {n q mu nw ny nv : ι → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.distributedObserve_sound (nb : ∀ i, Fin (q i) → ι)
    (A : ∀ i (a : Fin (q i)), Mat ℝ (n i) (n (nb i a))) (B : ∀ i, Mat ℝ (n i) (mu i))
    (Dw : ∀ i, Mat ℝ (n i) (nw i)) (C : ∀ i, Mat ℝ (ny i) (n i)) (Dv : ∀ i, Mat ℝ (ny i) (nv i))
    (Λ : ∀ i, Mat ℝ (n i) (ny i)) (red : ∀ i, Zonotope (Vec ℝ (n i)) → Zonotope (Vec ℝ (n i)))
    (hred : ∀ i Z, Z.construct ⊆ (red i Z).construct) (X : ℕ → ∀ i, Zonotope (Vec ℝ (n i)))
    (u : ℕ → ∀ i, Vec ℝ (mu i)) (y : ℕ → ∀ i, Vec ℝ (ny i))
    (hX : ∀ k i, X (k + 1) i = red i (Zonotope.correctedStepDistributed (Λ i) (A i) (B i) (Dw i)
      (C i) (Dv i) (u k i) (y (k + 1) i) (fun a => X k (nb i a))))
    (x : ℕ → ∀ i, Vec ℝ (n i)) (ϖ : ℕ → ∀ i, Vec ℝ (nw i)) (σ : ℕ → ∀ i, Vec ℝ (nv i))
    (hϖ : ∀ k i j, |ϖ k i j| ≤ 1) (hσ : ∀ k i j, |σ k i j| ≤ 1)
    (hx : ∀ k i, x (k + 1) i = ∑ a, A i a *ᵥ x k (nb i a) + B i *ᵥ u k i + Dw i *ᵥ ϖ k i)
    (hy : ∀ k i, y k i = C i *ᵥ x k i + Dv i *ᵥ σ k i)
    (h0 : ∀ i, x 0 i ∈ (X 0 i).construct) : -- --- CONCL ---
    ∀ k i, x k i ∈ (X k i).construct := by -- --- PROOF ---
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    intro i
    rw [hX k i]
    refine hred i _ ?_
    rw [hx k i]
    refine Zonotope.correctedStepDistributed_outer (Λ i) (A i) (B i) (Dw i) (C i) (Dv i) (u k i)
      (y (k + 1) i) (fun a => X k (nb i a)) (fun a => x k (nb i a)) (fun a => ih (nb i a))
      (ϖ k i) (hϖ k i) (σ (k + 1) i) (hσ (k + 1) i) ?_
    rw [← hx k i]
    exact hy (k + 1) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
