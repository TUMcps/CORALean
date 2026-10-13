import CORALean.ContSet.Zonotope.Real.Operations.DiffusionProp
import CORALean.ContSet.Zonotope.Real.Theorems.DiffusionPropStepOuter

/-!
# The set-propagation diffusion observer holds the true state

[1, Alg. 2] run over time: a state sequence `x_k = F x_{k-1} + Q_k β_k`, `|β_k| ≤ 1` (Eq. 27 of
[1, Thm. 2] with `n_k ∈ ⟨0, Q_k⟩`), from `x_0 ∈ Z₀`, whose outputs at instant `k` meet every
node's strips at the state of the previous instant, `|Γⁱ x_{k-1} - ȳⁱ_k| ≤ rⁱ_k`, is in the
zonotope of every node at every instant (`diffusionProp`). Induction on `k` with
`diffusionPropStep_outer`. The positivity of `tr(Ḡʲ Ḡʲᵀ)` of [1, Prop. 1] is assumed for the
zonotopes the run produces.
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

theorem Zonotope.diffusionProp_outer [∀ i, NeZero (m i)] (F : Mat ℝ n n) (Q : ℕ → Mat ℝ n nq)
    (Γ : ∀ i, Mat ℝ (p i) n) (r yb : ℕ → ∀ i, Vec ℝ (p i)) (nb : ∀ i, Fin (m i) → Fin N) (o : ℕ)
    (Z₀ : Zonotope (Vec ℝ n)) (x : ℕ → Vec ℝ n) (β : ℕ → Vec ℝ nq)
    (hβ : ∀ k j, |β k j| ≤ 1) (h0 : x 0 ∈ Z₀.construct)
    (hxs : ∀ k, x (k + 1) = F *ᵥ x k + Q (k + 1) *ᵥ β (k + 1))
    (hy : ∀ k i j, |(Γ i *ᵥ x k - yb (k + 1) i) j| ≤ r (k + 1) i j)
    (hα : ∀ k i a, 0 < ∑ s, ∑ l, ((Zonotope.diffusionPropLuenberger F (Q (k + 1)) Γ (r (k + 1))
      (yb (k + 1)) (Zonotope.diffusionProp F Q Γ r yb nb o Z₀ k) (nb i a)).G l s) ^ 2)
    (k : ℕ) (i : Fin N) :
    x k ∈ (Zonotope.diffusionProp F Q Γ r yb nb o Z₀ k i).construct := by -- --- PROOF ---
  induction k generalizing i with
  | zero => exact h0
  | succ k ih =>
    rw [hxs k]
    exact Zonotope.diffusionPropStep_outer F (Q (k + 1)) Γ (r (k + 1)) (yb (k + 1)) nb o _ (x k)
      (β (k + 1)) (hβ (k + 1)) ih (hy k) (hα k) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
