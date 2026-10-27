module

public import CORALean.NN.Layers.Theorems.Real.AbsSubEvalPolyDerivLe
public import CORALean.NN.Layers.Theorems.Real.ExistsEvalPolyNear
public import CORALean.NN.Layers.Theorems.Real.SampleGridMemIcc
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

/-!
# Refinement by order converges

ℝ-only, the sampling and the fit being exact. Weierstrass gives a polynomial within `ε` of `σ`,
so the half-range sampling converges to is itself driven to zero by raising the order. It does
not close as one limit: `M`, a bound on `|σ' - p'|`, may blow up with the degree, so for every
`ε` the statement gives an order *and* a sample count, `N` free to depend on the degree — which
is what refinement [1] does anyway.

## Inputs
* `σ` – activation function
* `σ'` – its derivative
* `l` – lower end of the interval
* `u` – upper end of the interval
* `Mσ` – bound on the derivative
* `ε` – accuracy

## Hypotheses
* `hd` – the activation has the given derivative
* `hσ` – the derivative is bounded on the interval
* `hlu` – interval is ordered
* `hε` – accuracy is positive

## Conclusion
* some fit and sample count give a sampling error below the accuracy

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../../../references/2023/ladner-hscc-abstraction-refinement.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_fit_samplingError_lt {σ σ' : ℝ → ℝ} {l u Mσ ε : ℝ}
    (hd : ∀ x, HasDerivAt σ (σ' x) x) (hσ : ∀ x, l ≤ x → x ≤ u → |σ' x| ≤ Mσ)
    (hlu : l ≤ u) (hε : 0 < ε) : -- --- CONCL ---
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ) (M : ℝ) (N : ℕ), 0 < N
      ∧ (∀ x, l ≤ x → x ≤ u → |σ' x - evalPolyDeriv c x| ≤ M)
      ∧ samplingError (fun x => σ x - evalPoly c x) M l u N < ε := by -- --- PROOF ---
  have hcont : ContinuousOn σ (Set.Icc l u) :=
    fun x _ => ((hd x).continuousAt).continuousWithinAt
  -- a quarter of the budget goes on the fit, which fixes the order and with it `M`
  obtain ⟨n, c, hfit⟩ := exists_evalPoly_near hcont (show (0:ℝ) < ε / 4 by linarith)
  refine ⟨n, c, polyDerivDiff (-Mσ) Mσ (polyDerivCenter c) (polyDerivRadius c l u), ?_⟩
  have hMbound : ∀ x, l ≤ x → x ≤ u →
      |σ' x - evalPolyDeriv c x|
        ≤ polyDerivDiff (-Mσ) Mσ (polyDerivCenter c) (polyDerivRadius c l u) := by
    intro x hx hx'
    obtain ⟨h₁, h₂⟩ := abs_le.mp (hσ x hx hx')
    exact abs_sub_evalPolyDeriv_le h₁ h₂ hx hx'
  have hM0 : 0 ≤ polyDerivDiff (-Mσ) Mσ (polyDerivCenter c) (polyDerivRadius c l u) :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  set M := polyDerivDiff (-Mσ) Mσ (polyDerivCenter c) (polyDerivRadius c l u) with hMdef
  -- and half of it on the padding, which only now can be asked to be small
  obtain ⟨N, hNgt⟩ := exists_nat_gt (max 1 (2 * (M * (u - l)) / ε))
  have hmax1 : (1:ℝ) ≤ max 1 (2 * (M * (u - l)) / ε) := le_max_left _ _
  have hNpos : (0:ℝ) < N := lt_of_le_of_lt (by linarith) hNgt
  have hN : 0 < N := Nat.cast_pos.mp hNpos
  have hpad : M * ((u - l) / N) < ε / 2 := by
    have h2 : 2 * (M * (u - l)) / ε < N := lt_of_le_of_lt (le_max_right _ _) hNgt
    rw [div_lt_iff₀ hε] at h2
    rw [← mul_div_assoc, div_lt_iff₀ hNpos]
    linarith
  -- the samples lie in the box, so the fit's own bound caps the sampled range
  have hgb : ∀ i : Fin (N + 1),
      |σ (sampleGrid l u N i) - evalPoly c (sampleGrid l u N i)| ≤ ε / 4 := by
    intro i
    obtain ⟨ha, hb⟩ := sampleGrid_mem_Icc hN hlu i
    exact hfit _ ha hb
  have hsup : sampleSup (fun x => σ x - evalPoly c x) l u N ≤ ε / 4 :=
    Finset.sup'_le _ _ fun i _ => (abs_le.mp (hgb i)).2
  have hinf : -(ε / 4) ≤ sampleInf (fun x => σ x - evalPoly c x) l u N :=
    Finset.le_inf' _ _ fun i _ => (abs_le.mp (hgb i)).1
  refine ⟨N, hN, hMbound, ?_⟩
  show (sampleSup (fun x => σ x - evalPoly c x) l u N
    - sampleInf (fun x => σ x - evalPoly c x) l u N) / 2 + M * ((u - l) / N) < ε
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
