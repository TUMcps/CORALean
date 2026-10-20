module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.DependentTermsMatZono
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpW
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# `MatExp.dependentTermsMatZono` contains the exact terms of every member

Expand `(C + Σ βᵢ Gᵢ)²` and split the double sum of `βᵢ βⱼ Gᵢ Gⱼ` into the diagonal and each pair `i
< j` once (`aux_double_sum`). The diagonal uses `βᵢ² = ½ + ½ (2βᵢ² - 1)`, so the three blocks take
the coefficients `βᵢ`, `2βᵢ² - 1` and `βᵢ βⱼ`, all in `[-1, 1]`, and `zSq` holds `r² M²`. Then `zH`
is `I + r M + ½ r² M²` by the same coefficients: its generators are half those of `zSq` and `r Gᵢ`
on the first block.

## Inputs
* `Z` – matrix zonotope
* `r` – step length
* `M` – member matrix

## Hypotheses
* `hM` – member lies in the matrix zonotope

## Conclusion
* the exact terms of the member lie in the dependent terms
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every ordered pair is below the diagonal, on it or above it: the double sum is the diagonal plus
each unordered pair once, in both orders. -/
theorem MatExp.aux_double_sum {α : Type} [AddCommMonoid α] {h : ℕ} (f : Fin h → Fin h → α) :
    ∑ i, ∑ j, f i j = ∑ i, f i i +
      ∑ p ∈ Finset.univ.filter (fun p : Fin h × Fin h => p.1 < p.2),
        (f p.1 p.2 + f p.2 p.1) := by -- --- PROOF ---
  -- each ordered pair is below the diagonal, on it or above it
  have hpt : ∀ i j : Fin h, f i j = (if i < j then f i j else 0) + (if i = j then f i j else 0)
      + (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, hij.ne, hij.not_gt]
    · subst hij; simp
    · simp [hij, hij.ne', hij.not_gt]
  have hsw : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f j i else 0) :=
    Finset.sum_comm
  have hAB : ∑ i, ∑ j, (if i < j then f i j + f j i else 0) =
      (∑ i, ∑ j, if i < j then f i j else 0) + ∑ i, ∑ j, (if i < j then f j i else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  -- the three parts, the middle one the diagonal, the last swapped onto the first
  calc ∑ i, ∑ j, f i j
      = ∑ i, ∑ j, ((if i < j then f i j else 0) + (if i = j then f i j else 0)
        + (if j < i then f i j else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
    _ = ∑ i, f i i + ∑ i, ∑ j, (if i < j then f i j + f j i else 0) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, hsw]
        rw [hAB]
        abel
    _ = _ := by
        congr 1
        rw [Finset.sum_filter]
        exact (Fintype.sum_prod_type' (f := fun i j => if i < j then f i j + f j i else 0)).symm


-- =======================================  MAIN THEOREM  ======================================= --

/-- The square and `I + M r + ½ M² r²` of every member lie in `zSq` and `zH`. -/
theorem MatExp.dependentTermsMatZono_outer (Z : Zonotope (Mat ℝ n n)) (r : ℝ) {M : Mat ℝ n n}
    (hM : M ∈ Z.construct) :
    r ^ 2 • (M * M) ∈ (MatExp.dependentTermsMatZono Z r).zSq.construct ∧
      1 + MatExp.expW M r ∈ (MatExp.dependentTermsMatZono Z r).zH.construct := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hM
  -- the member `c + Σ βᵢ Gᵢ`, and the pairs `i < j` in the order the generators are listed
  simp only [MatExp.dependentTermsMatZono]
  set c := Z.c with hc
  set G := Z.G with hG
  set ind := Finset.univ.filter fun p : Fin Z.h × Fin Z.h => p.1 < p.2 with hind
  set pr : Fin ind.card → Fin Z.h × Fin Z.h := fun k => (ind.equivFin.symm k).1 with hpr
  -- the coefficients of the three blocks: `βᵢ`, `2βᵢ² - 1` and `βᵢβⱼ`, all in `[-1, 1]`
  let γ : Fin (Z.h + Z.h + ind.card) → ℝ :=
    Fin.append (Fin.append β (fun i => 2 * β i ^ 2 - 1)) (fun k => β (pr k).1 * β (pr k).2)
  have hγ : ∀ k, |γ k| ≤ 1 := by
    intro k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · simpa [γ] using hβ i
      · have := hβ i
        rw [abs_le] at this ⊢
        simp only [γ, Fin.append_left, Fin.append_right]
        constructor <;> nlinarith [this.1, this.2]
    · simp only [γ, Fin.append_right]
      rw [abs_mul]
      exact mul_le_one₀ (hβ _) (abs_nonneg _) (hβ _)
  -- the three generator blocks, summed one at a time
  have hsplit : ∀ F : Fin (Z.h + Z.h + ind.card) → Mat ℝ n n, ∑ k, F k =
      ∑ i : Fin Z.h, F (Fin.castAdd _ (Fin.castAdd _ i))
      + ∑ i : Fin Z.h, F (Fin.castAdd _ (Fin.natAdd _ i))
      + ∑ k : Fin ind.card, F (Fin.natAdd _ k) := by
    intro F
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
  -- the square of the member, with its double sum
  have hexp : (c + ∑ i, β i • G i) * (c + ∑ i, β i • G i) = c * c
      + ∑ i, β i • (c * G i + G i * c) + ∑ i, ∑ j, (β i * β j) • (G i * G j) := by
    have h1 : c * ∑ i, β i • G i = ∑ i, β i • (c * G i) := by
      rw [Finset.mul_sum]; simp only [mul_smul_comm]
    have h2 : (∑ i, β i • G i) * c = ∑ i, β i • (G i * c) := by
      rw [Finset.sum_mul]; simp only [smul_mul_assoc]
    have h3 : (∑ i, β i • G i) * ∑ i, β i • G i = ∑ i, ∑ j, (β i * β j) • (G i * G j) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_mul_smul_comm _ _ _ _
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h1, h2, h3]
    simp only [smul_add, Finset.sum_add_distrib]
    abel
  -- the double sum is the diagonal and each pair once
  have hD : ∑ i, ∑ j, (β i * β j) • (G i * G j) = ∑ i, (β i * β i) • (G i * G i)
      + ∑ p ∈ ind, (β p.1 * β p.2) • (G p.1 * G p.2 + G p.2 * G p.1) := by
    rw [MatExp.aux_double_sum (fun i j => (β i * β j) • (G i * G j))]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_add, mul_comm (β p.2) (β p.1)]
  -- the three block sums, scaled by `r²`
  have hA : ∑ i, β i • (r ^ 2 • (c * G i + G i * c)) = r ^ 2 • ∑ i, β i • (c * G i + G i * c) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have hB : ∑ i, (2 * β i ^ 2 - 1) • ((r ^ 2 / 2) • (G i * G i))
      = r ^ 2 • ∑ i, (β i * β i) • (G i * G i) - (r ^ 2 / 2) • ∑ i, G i * G i := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    module
  have hC : ∑ k : Fin ind.card, (β (pr k).1 * β (pr k).2) • (r ^ 2 • (G (pr k).1 * G (pr k).2
      + G (pr k).2 * G (pr k).1)) = r ^ 2 • ∑ p ∈ ind, (β p.1 * β p.2) • (G p.1 * G p.2
      + G p.2 * G p.1) := by
    rw [Finset.smul_sum]
    have h := Equiv.sum_comp ind.equivFin.symm (fun x : ind => (β x.1.1 * β x.1.2) •
      (r ^ 2 • (G x.1.1 * G x.1.2 + G x.1.2 * G x.1.1)))
    rw [Finset.sum_coe_sort ind (fun p => (β p.1 * β p.2) •
      (r ^ 2 • (G p.1 * G p.2 + G p.2 * G p.1)))] at h
    rw [show (∑ k : Fin ind.card, (β (pr k).1 * β (pr k).2) • (r ^ 2 • (G (pr k).1 * G (pr k).2
      + G (pr k).2 * G (pr k).1))) = ∑ k : Fin ind.card, (fun x : ind => (β x.1.1 * β x.1.2) •
      (r ^ 2 • (G x.1.1 * G x.1.2 + G x.1.2 * G x.1.1))) (ind.equivFin.symm k) from rfl, h]
    exact Finset.sum_congr rfl fun p _ => smul_comm _ _ _
  -- the square of the member is `sqC` plus the three blocks
  have key : r ^ 2 • ((c + ∑ i, β i • G i) * (c + ∑ i, β i • G i)) =
      r ^ 2 • (c * c + (1 / 2 : ℝ) • ∑ i, G i * G i)
      + (∑ i, β i • (r ^ 2 • (c * G i + G i * c))
      + ∑ i, (2 * β i ^ 2 - 1) • ((r ^ 2 / 2) • (G i * G i))
      + ∑ k : Fin ind.card, (β (pr k).1 * β (pr k).2) • (r ^ 2 • (G (pr k).1 * G (pr k).2
      + G (pr k).2 * G (pr k).1))) := by
    rw [hexp, hD, hA, hB, hC]
    module
  refine ⟨?_, ?_⟩
  · -- `zSq`
    refine ⟨γ, hγ, ?_⟩
    rw [hsplit]
    simp only [γ, Fin.append_left, Fin.append_right]
    exact key
  · -- `zH`: half the blocks of `zSq`, and `r Gᵢ` on the first
    refine ⟨γ, hγ, ?_⟩
    rw [hsplit]
    simp only [γ, Fin.append_left, Fin.append_right]
    have h1 : ∑ i, β i • ((1 / 2 : ℝ) • (r ^ 2 • (c * G i + G i * c)) + r • G i)
        = (1 / 2 : ℝ) • ∑ i, β i • (r ^ 2 • (c * G i + G i * c)) + r • ∑ i, β i • G i := by
      rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by module
    have h2 : ∑ i, (2 * β i ^ 2 - 1) • ((1 / 2 : ℝ) • ((r ^ 2 / 2) • (G i * G i)))
        = (1 / 2 : ℝ) • ∑ i, (2 * β i ^ 2 - 1) • ((r ^ 2 / 2) • (G i * G i)) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by module
    have h3 : ∑ k : Fin ind.card, (β (pr k).1 * β (pr k).2) • ((1 / 2 : ℝ) • (r ^ 2 •
        (G (pr k).1 * G (pr k).2 + G (pr k).2 * G (pr k).1)))
        = (1 / 2 : ℝ) • ∑ k : Fin ind.card, (β (pr k).1 * β (pr k).2) • (r ^ 2 •
        (G (pr k).1 * G (pr k).2 + G (pr k).2 * G (pr k).1)) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => by module
    rw [h1, h2, h3]
    -- the terms of `I + M r + ½ M² r²` against `key`
    simp only [MatExp.expW]
    linear_combination (norm := module) (1 / 2 : ℝ) • key

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
