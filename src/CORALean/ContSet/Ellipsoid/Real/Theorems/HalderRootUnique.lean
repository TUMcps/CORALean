import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderStationarityStrictAntiOn
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Monoid

/-!
# Halder's stationarity equation has a unique positive root

[1, Thm. 2]: the equation `∑ᵢ (1 − β²λᵢ)/(1 + βλᵢ) = 0` of [1, Eq. 18] has exactly one
positive root for positive `λᵢ`. The printed proof counts sign changes of the coefficients
(24) by Descartes' rule and leans on [1, Cor. 1], which is false; here the left side is
strictly decreasing, positive at `0` and negative at `1 + ∑ 1/λᵢ`, so it crosses zero once.

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {ι : Type*} [Fintype ι]
variable {lam : ι → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2]: [1, Eq. 18] has a unique positive root, whatever the dimension. -/
theorem Ellipsoid.exists_unique_halderStationarity_root [Nonempty ι] (hlam : ∀ i, 0 < lam i) :
    ∃! β : ℝ, 0 < β ∧ Ellipsoid.halderStationarity lam β = 0 := by -- --- PROOF ---
  have hcont : ContinuousOn (Ellipsoid.halderStationarity lam) (Set.Ici 0) := by
    unfold Ellipsoid.halderStationarity
    refine continuousOn_finsetSum _ fun i _ => ?_
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    have := hlam i
    have : (0:ℝ) ≤ x := hx
    positivity
  -- continuous on `[0, ∞)`, equal to `d` at `0`
  have hcard : Ellipsoid.halderStationarity lam 0 = Fintype.card ι := by
    simp [Ellipsoid.halderStationarity]
  have hpos : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  -- past `1 + ∑ 1/λᵢ` every term is negative
  set β₁ : ℝ := 1 + ∑ i, 1 / lam i with hβ₁
  have hsum : 0 < ∑ i, 1 / lam i := Finset.sum_pos (fun i _ => one_div_pos.2 (hlam i))
    Finset.univ_nonempty
  have hneg : Ellipsoid.halderStationarity lam β₁ < 0 := by
    refine Finset.sum_neg (fun i _ => ?_) Finset.univ_nonempty
    have hi : 1 / lam i ≤ ∑ j, 1 / lam j :=
      Finset.single_le_sum (f := fun j => 1 / lam j) (fun j _ => (one_div_pos.2 (hlam j)).le)
        (Finset.mem_univ i)
    have h1 : 1 < β₁ * lam i := by
      have : 1 / lam i < β₁ := by linarith
      rw [div_lt_iff₀ (hlam i)] at this
      linarith
    have h2 : 1 < β₁ ^ 2 * lam i := by nlinarith [hlam i, hsum]
    exact div_neg_of_neg_of_pos (by linarith) (by have := hlam i; positivity)
  -- so it crosses zero between `0` and `β₁`, and only once
  obtain ⟨β, hβ, hβ0⟩ : ∃ β ∈ Set.Ioo (0:ℝ) β₁, Ellipsoid.halderStationarity lam β = 0 := by
    have hc : ContinuousOn (Ellipsoid.halderStationarity lam) (Set.Icc 0 β₁) :=
      hcont.mono Set.Icc_subset_Ici_self
    exact intermediate_value_Ioo' (by linarith : (0:ℝ) ≤ β₁) hc ⟨hneg, by rw [hcard]; exact hpos⟩
  refine ⟨β, ⟨hβ.1, hβ0⟩, fun γ ⟨hγ, hγ0⟩ => ?_⟩
  exact (Ellipsoid.halderStationarity_strictAntiOn hlam).injOn (Set.mem_Ici.2 hγ.le)
    (Set.mem_Ici.2 hβ.1.le) (by rw [hγ0, hβ0])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
