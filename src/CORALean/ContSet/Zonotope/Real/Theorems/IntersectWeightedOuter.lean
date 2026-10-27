module

public import CORALean.ContSet.Zonotope.Real.Operations.IntersectWeighted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.BigOperators

@[expose] public section

/-!
# `Zonotope.intersectWeighted` encloses the intersection of the zonotopes

[1, Lemma 3]: a point `x` of every `Zᵢ = cᵢ + Gᵢ βᵢ` satisfies `x = (Σ wᵢ)⁻¹ Σ wᵢ (cᵢ + Gᵢ βᵢ)`,
which is the center plus the weighted generators at the stacked coefficients `(β₁, …, β_d)`,
each still in `[-1, 1]`. Any weights with a nonzero sum, positive or not; outer only.

## Inputs
* `w` – weights
* `Zs` – zonotopes

## Hypotheses
* `hw` – weights sum to nonzero

## Conclusion
* the intersection lies in the weighted zonotope

## References

* [1] [A. Alanwar, V. Gaßmann, X. He, H. Said, H. Sandberg, K. H. Johansson and M. Althoff.
      "Privacy-Preserving Set-Based Estimation Using Partially Homomorphic Encryption". European
      Journal of Control,
      2023.](../../../../../../references/2023/alanwar-ejc-privacy-preserving-estimation.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.intersectWeighted_outer (w : Fin d → ℝ) (Zs : Fin d → Zonotope (Vec ℝ n))
    (hw : ∑ i, w i ≠ 0) : -- --- CONCL ---
    (⋂ i, (Zs i).construct) ⊆ (Zonotope.intersectWeighted w Zs).construct := by -- --- PROOF ---
  intro x hx
  -- every zonotope has its own coefficients for `x`
  have hx' : ∀ i, ∃ β : Fin (Zs i).h → ℝ, (∀ j, |β j| ≤ 1) ∧
      x = (Zs i).c + ∑ j, β j • (Zs i).G j := fun i => Set.mem_iInter.mp hx i
  choose β hβ hxβ using hx'
  -- coefficients and weighted generators on the sigma type, read through the index equivalence
  let β' : (i : Fin d) × Fin (Zs i).h → ℝ := fun s => β s.1 s.2
  let G'' : (i : Fin d) × Fin (Zs i).h → Vec ℝ n := fun s =>
    (∑ i, w i)⁻¹ • (w s.1 • (Zs s.1).G s.2)
  refine ⟨fun q => β' (finSigmaFinEquiv.symm q), fun q => hβ _ _, ?_⟩
  -- the stacked sum is the weighted sum of the zonotopes' own sums
  have hsum : ∑ q : Fin (∑ i, (Zs i).h), β' (finSigmaFinEquiv.symm q) •
      G'' (finSigmaFinEquiv.symm q) =
      (∑ i, w i)⁻¹ • ∑ i, w i • ∑ j, β i j • (Zs i).G j := by
    rw [← Equiv.sum_comp finSigmaFinEquiv, Fintype.sum_sigma]
    simp only [Finset.smul_sum, Equiv.symm_apply_apply, β', G'']
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm (β i j), smul_comm (β i j)]
  -- `x = (Σ w)⁻¹ Σ wᵢ x`, each `x` written through its own zonotope
  have hxw : x = (∑ i, w i)⁻¹ • ∑ i, w i • ((Zs i).c + ∑ j, β i j • (Zs i).G j) := by
    simp_rw [← hxβ]
    rw [← Finset.sum_smul, smul_smul, inv_mul_cancel₀ hw, one_smul]
  show x = (∑ i, w i)⁻¹ • ∑ i, w i • (Zs i).c + ∑ q : Fin (∑ i, (Zs i).h),
    β' (finSigmaFinEquiv.symm q) • G'' (finSigmaFinEquiv.symm q)
  rw [hsum]
  conv_lhs => rw [hxw]
  simp only [smul_add, Finset.sum_add_distrib]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
