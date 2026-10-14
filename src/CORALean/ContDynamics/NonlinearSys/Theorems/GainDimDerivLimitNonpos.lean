module

public import CORALean.ContDynamics.NonlinearSys.Theorems.GainDimDerivTendsto

@[expose] public section

/-!
# The gain's derivative has a non-positive limit when `g'(0)/g(0) ≥ 0`

`[1, Prop. 2 (derivative)]`'s `(41)`: `lim_{h→0} dφᵢ(h;δ)/dh ≤ 0` for `δ ∈ [0,1]`. By
`gainDim_deriv_tendsto` the limit exists and is `δ^{qᵢ+1}(δ − 1)·g'(0)/g(0)`, so it is
non-positive exactly when `g'(0)/g(0) ≥ 0`, that is when the width
`dᵢ(box(R^∞_abs(t))) = t^{qᵢ+1}g(t)` does not lose relative size to its leading term as `t` leaves
`0`. That is the correction `(41)` needs: with every `Q⁽ᵖ⁾ᵢ` constant `g'(0)` is the non-negative
coefficient of `t^{qᵢ+2}` and the condition holds. `GainDeriv` has `g'(0)/g(0) < 0`
and a positive limit.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter Topology

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, Prop. 2 (derivative)]`'s `(41)` for `δ ∈ [0,1]`, with the condition `0 ≤ g'(0)/g(0)` that
makes it true: the derivative of the gain tends to a limit, and the limit is at most `0`. -/
theorem gainDim_deriv_limit_nonpos (A : ℝ → Mat ℝ n n) (Ψ : ℝ → Set (Vec ℝ n)) (i : Fin n)
    {qi : ℕ} {g g' : ℝ → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hg : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt g (g' t) t) (hg' : ContinuousAt g' 0) (hg0 : g 0 ≠ 0)
    (hexp : ∀ᶠ t in 𝓝[≥] (0:ℝ), boxDiameter (abstrSolInf A Ψ t) i = t ^ (qi + 1) * g t)
    (hgrow : 0 ≤ g' 0 / g 0) :
    ∃ L : ℝ, L ≤ 0 ∧ Tendsto (fun h => deriv (fun s => gainDim A Ψ s δ i) h) (𝓝[>] (0:ℝ))
      (𝓝 L) := by -- --- PROOF ---
  refine ⟨δ ^ (qi + 1) * (δ - 1) * g' 0 / g 0, ?_,
    gainDim_deriv_tendsto A Ψ i hδ0 hδ1 hg hg' hg0 hexp⟩
  have : δ ^ (qi + 1) * (δ - 1) * g' 0 / g 0 = (δ ^ (qi + 1) * (δ - 1)) * (g' 0 / g 0) := by ring
  rw [this]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hδ0 _) (by linarith)) hgrow

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
