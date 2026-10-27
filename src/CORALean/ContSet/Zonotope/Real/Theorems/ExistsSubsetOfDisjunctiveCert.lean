module

public import CORALean.ContSet.Zonotope.Real.Theorems.SubsetOfCert
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Disjunctive zonotope containment, sufficiently

`[1, Cor. 5]`: `⟨x̄, X⟩` lies in one of `⟨ȳᵢ, Yᵢ⟩` if `‖(Γᵢ | βᵢ)‖∞ ≤ δᵢ ∈ {0, 1}`,
`∑ δᵢ = 1`, `∑ᵢ (Yᵢ βᵢ + δᵢ ȳᵢ) = x̄` and `∑ᵢ Yᵢ Γᵢ = X` (`[1, Cor. 5, Eq. 35]`). The summands
with `δᵢ = 0` have `Γᵢ = 0` and `βᵢ = 0`, so the one with `δᵢ = 1` is `[1, Thm. 3]`'s
certificate, `βᵢ` with its sign flipped.

## Inputs
* `Zx` – inner zonotope
* `Zy` – family of candidate outer zonotopes
* `Γ` – generator coefficient matrices
* `β` – center coefficients
* `δ` – selection indicators

## Hypotheses
* `hδ` – indicators zero or one
* `hsum` – exactly one selected
* `hn` – row sums bounded by the indicator
* `hc` – centers agree
* `hX` – generators agree

## Conclusion
* `Zx` lies in one of the candidates

## References

* [1] [S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". 2019 IEEE
      58th Conference on Decision and Control (CDC),
      2019.](../../../../../../references/2019/sadraddini-cdc-polytope-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.exists_subset_of_disjunctive_cert (Zx : Zonotope α) (Zy : Fin N → Zonotope α)
    (Γ : (i : Fin N) → Mat ℝ (Zy i).h Zx.h) (β : (i : Fin N) → Vec ℝ (Zy i).h)
    (δ : Fin N → ℝ) (hδ : ∀ i, δ i = 0 ∨ δ i = 1) (hsum : ∑ i, δ i = 1)
    (hn : ∀ i k, ∑ j, |Γ i k j| + |β i k| ≤ δ i)
    (hc : ∑ i, ((∑ k, β i k • (Zy i).G k) + δ i • (Zy i).c) = Zx.c)
    (hX : ∀ j, ∑ i, ∑ k, Γ i k j • (Zy i).G k = Zx.G j) : -- --- CONCL ---
    ∃ i, Zx.construct ⊆ (Zy i).construct := by -- --- PROOF ---
  have hδ0 : ∀ i, 0 ≤ δ i := fun i => by rcases hδ i with h | h <;> simp [h]
  obtain ⟨i₀, hi₀⟩ : ∃ i, δ i = 1 := by
    by_contra hno
    push Not at hno
    have : ∑ i, δ i = 0 := Finset.sum_eq_zero fun i _ => (hδ i).resolve_right (hno i)
    linarith
  -- every other weight is `0`, so its `Γ` and `β` vanish
  have hothers : ∀ j, j ≠ i₀ → δ j = 0 := by
    intro j hj
    refine (hδ j).resolve_right fun hj1 => ?_
    have := Finset.add_le_sum (f := δ) (fun i _ => hδ0 i) (Finset.mem_univ i₀)
      (Finset.mem_univ j) (Ne.symm hj)
    linarith
  -- a zero row sum bound leaves no room for any entry
  have hΓ0 : ∀ j, j ≠ i₀ → ∀ k l, Γ j k l = 0 := by
    intro j hj k l
    have h := hn j k
    rw [hothers j hj] at h
    have hle : |Γ j k l| ≤ ∑ l', |Γ j k l'| :=
      Finset.single_le_sum (f := fun l' => |Γ j k l'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ l)
    exact abs_nonpos_iff.mp (by linarith [abs_nonneg (β j k)])
  have hβ0 : ∀ j, j ≠ i₀ → ∀ k, β j k = 0 := by
    intro j hj k
    have h := hn j k
    rw [hothers j hj] at h
    have hs : 0 ≤ ∑ l, |Γ j k l| := Finset.sum_nonneg fun l _ => abs_nonneg _
    exact abs_nonpos_iff.mp (by linarith)
  -- what is left is `[1, Thm. 3]` at `i₀`, `β` negated
  refine ⟨i₀, Zonotope.construct_subset_of_cert Zx (Zy i₀) (Γ i₀) (-β i₀) (fun j => ?_) ?_
    fun k => by simpa [abs_neg, hi₀] using hn i₀ k⟩
  · rw [← hX j, Finset.sum_eq_single i₀ (fun i _ hi => Finset.sum_eq_zero fun k _ => by
      rw [hΓ0 i hi, zero_smul]) (by simp)]
  · rw [← hc, Finset.sum_eq_single i₀ (fun i _ hi => by
      rw [hothers i hi, zero_smul, add_zero]
      exact Finset.sum_eq_zero fun k _ => by rw [hβ0 i hi, zero_smul]) (by simp), hi₀, one_smul]
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
