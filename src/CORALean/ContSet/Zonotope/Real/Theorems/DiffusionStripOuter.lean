module

public import CORALean.ContSet.Zonotope.Real.Operations.DiffusionStrip
public import CORALean.ContSet.Zonotope.Real.Theorems.DiffusionStripStepOuter

@[expose] public section

/-!
# The strip-based diffusion observer holds the true state

[1, Alg. 1] run over time: a state sequence `x_{k+1} = F x_k + Q_k β_k`, `|β_k| ≤ 1` (the system
of Eq. 8 of [1] with `n_k ∈ ⟨0, Q_k⟩`), from `x_0 ∈ Z₀`, whose outputs meet every node's strips
`|Γⁱ x_k - ȳⁱ_k| ≤ rⁱ_k` at every instant, is in the predicted zonotope of every node at every
instant (`diffusionStrip`). Induction on `k` with `diffusionStripStep_outer`. The positivity of
`tr(Ḡʲ Ḡʲᵀ)` of [1, Prop. 1] is assumed for the zonotopes the run produces.

## Inputs
* `F` – dynamics matrix
* `Q` – process-noise generators per instant
* `Γ` – stacked measurement matrices
* `r` – noise radii per instant
* `yb` – outputs per instant
* `nb` – neighbour indices of each node
* `o` – reduction order
* `Z₀` – initial zonotope
* `x` – state trajectory
* `β` – process-noise coefficients per instant
* `k` – instant
* `i` – node

## Hypotheses
* `hβ` – coefficients within the unit box
* `h0` – initial state lies in `Z₀`
* `hxs` – trajectory follows the dynamics
* `hy` – outputs consistent with the trajectory
* `hα` – every neighbour trace positive

## Conclusion
* the true state lies in each node's predicted zonotope

## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      360(10):6976-6993, 2023. arXiv:2003.10347.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nq N : ℕ} {p m : Fin N → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.diffusionStrip_outer [∀ i, NeZero (m i)] (F : Mat ℝ n n) (Q : ℕ → Mat ℝ n nq)
    (Γ : ∀ i, Mat ℝ (p i) n) (r yb : ℕ → ∀ i, Vec ℝ (p i)) (nb : ∀ i, Fin (m i) → Fin N) (o : ℕ)
    (Z₀ : Zonotope (Vec ℝ n)) (x : ℕ → Vec ℝ n) (β : ℕ → Vec ℝ nq)
    (hβ : ∀ k j, |β k j| ≤ 1) (h0 : x 0 ∈ Z₀.construct)
    (hxs : ∀ k, x (k + 1) = F *ᵥ x k + Q k *ᵥ β k)
    (hy : ∀ k i j, |(Γ i *ᵥ x k - yb k i) j| ≤ r k i j)
    (hα : ∀ k i a, 0 < ∑ s, ∑ l, ((Zonotope.diffusionStripMeasurement Γ (r k) (yb k)
      (Zonotope.diffusionStrip F Q Γ r yb nb o Z₀ k) (nb i a)).G l s) ^ 2) (k : ℕ) (i : Fin N) :
    x k ∈ (Zonotope.diffusionStrip F Q Γ r yb nb o Z₀ k i).construct := by -- --- PROOF ---
  induction k generalizing i with
  | zero => exact h0
  | succ k ih =>
    rw [hxs k]
    exact Zonotope.diffusionStripStep_outer F (Q k) Γ (r k) (yb k) nb o _ (x k) (β k) (hβ k)
      ih (hy k) (hα k) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
