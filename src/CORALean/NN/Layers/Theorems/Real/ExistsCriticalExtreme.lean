import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The extremes of `ϕ - m x` are at the ends or where the slope is `m`

The reduction behind [1, Prop. 10] for a differentiable activation `ϕ` with derivative `ϕ'`: on
`[l, u]`, the function `ϕ(x) - m x` has a minimizer and a maximizer, each an endpoint or a point
where `ϕ'(x) = m`, the derivative of the difference vanishing at an interior extremum (Fermat).
For `tanh` and the logistic function, `ϕ' = m` is then solved for the points of `P_ϕ`.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_critical_extreme (ϕ ϕ' : ℝ → ℝ) (m l u : ℝ) (hd : ∀ x, HasDerivAt ϕ (ϕ' x) x)
    (hlu : l ≤ u) :
    (∃ q ∈ Set.Icc l u, (∀ y ∈ Set.Icc l u, ϕ q - m * q ≤ ϕ y - m * y) ∧
      (q = l ∨ q = u ∨ ϕ' q = m)) ∧
    (∃ q ∈ Set.Icc l u, (∀ y ∈ Set.Icc l u, ϕ y - m * y ≤ ϕ q - m * q) ∧
      (q = l ∨ q = u ∨ ϕ' q = m)) := by -- --- PROOF ---
  set g : ℝ → ℝ := fun x => ϕ x - m * x with hg
  have hgd : ∀ x, HasDerivAt g (ϕ' x - m) x := fun x => by
    have h := (hd x).sub ((hasDerivAt_id x).const_mul m)
    simp only [mul_one] at h
    exact h
  -- the extremes exist on the compact box
  have hcont : ContinuousOn g (Set.Icc l u) := fun x _ => (hgd x).continuousAt.continuousWithinAt
  have hne : (Set.Icc l u).Nonempty := ⟨l, Set.left_mem_Icc.2 hlu⟩
  obtain ⟨a, haI, ha⟩ := isCompact_Icc.exists_isMinOn hne hcont
  obtain ⟨b, hbI, hb⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  refine ⟨⟨a, haI, fun y hy => ha hy, ?_⟩, ⟨b, hbI, fun y hy => hb hy, ?_⟩⟩
  · -- an interior minimizer has derivative zero
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    have hI : Set.Icc l u ∈ nhds a :=
      Icc_mem_nhds (lt_of_le_of_ne haI.1 (Ne.symm h1)) (lt_of_le_of_ne haI.2 h2)
    exact h3 (by linarith [(ha.isLocalMin hI).hasDerivAt_eq_zero (hgd a)])
  · -- and so does an interior maximizer
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    have hI : Set.Icc l u ∈ nhds b :=
      Icc_mem_nhds (lt_of_le_of_ne hbI.1 (Ne.symm h1)) (lt_of_le_of_ne hbI.2 h2)
    exact h3 (by linarith [(hb.isLocalMax hI).hasDerivAt_eq_zero (hgd b)])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
