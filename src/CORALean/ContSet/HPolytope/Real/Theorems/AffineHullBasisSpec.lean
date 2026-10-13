import CORALean.ContSet.HPolytope.Real.Operations.AffineHullBasis
import CORALean.ContSet.HPolytope.Real.HPolytope
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# What `HPolytope.affineHullBasis` returns

[1, Alg. 2], given `c ∈ P` and a maximizer for each step — perpendicular to the columns so far,
completing a point of `P - c`, and at least as long as every such vector, up to the cap `φ` the
paper adds for unbounded `P`: the columns are pairwise orthogonal and nonzero, they lie in the
span of `P - c`, and every point of `P - c` is within `ε` of their span. At `ε = 0` that is the
paper's claim, `P - c ⊆ span(B)`: the columns are a basis of the affine hull's direction, of
minimal size. The text calls `B` orthonormal; line 8 appends `x_iter` unscaled, so it is
orthogonal. The paper's proof is the one here: the part of `z - c` perpendicular to `B` is a
candidate, so it is no longer than `x_iter`.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What the loop keeps true: orthogonal, nonzero columns in the span of `P - c`. -/
def aux_Inv (S : Submodule ℝ (Vec ℝ n)) (r : ℕ) (B : Fin r → Vec ℝ n) : Prop :=
  (∀ i j, i ≠ j → B i ⬝ᵥ B j = 0) ∧ (∀ i, B i ≠ 0) ∧ ∀ i, B i ∈ S

/-- Pairwise orthogonal nonzero vectors are linearly independent. -/
theorem aux_linearIndependent {r : ℕ} {B : Fin r → Vec ℝ n}
    (horth : ∀ i j, i ≠ j → B i ⬝ᵥ B j = 0) (hne : ∀ i, B i ≠ 0) :
    LinearIndependent ℝ B := by -- --- PROOF ---
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrArg (· ⬝ᵥ B i) hg
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at h
  rw [Finset.sum_eq_single_of_mem i hi fun k _ hki => by rw [horth k i hki, mul_zero]] at h
  have hii : B i ⬝ᵥ B i ≠ 0 := fun h0 => hne i (dotProduct_self_eq_zero.mp h0)
  exact (mul_eq_zero.mp h).resolve_right hii

/-- The part of `u` along orthogonal nonzero columns, and what is left is perpendicular. -/
theorem aux_proj {r : ℕ} {B : Fin r → Vec ℝ n} (horth : ∀ i j, i ≠ j → B i ⬝ᵥ B j = 0)
    (hne : ∀ i, B i ≠ 0) (u : Vec ℝ n) :
    (∑ i, (u ⬝ᵥ B i / B i ⬝ᵥ B i) • B i) ∈ Submodule.span ℝ (Set.range B) ∧
      ∀ j, B j ⬝ᵥ (u - ∑ i, (u ⬝ᵥ B i / B i ⬝ᵥ B i) • B i) = 0 := by -- --- PROOF ---
  refine ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩),
    fun j => ?_⟩
  rw [dotProduct_sub, dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul]
  rw [Finset.sum_eq_single j (fun k _ hkj => by rw [horth j k (Ne.symm hkj), mul_zero])
    (fun h => absurd (Finset.mem_univ j) h)]
  have hjj : B j ⬝ᵥ B j ≠ 0 := fun h0 => hne j (dotProduct_self_eq_zero.mp h0)
  rw [div_mul_cancel₀ _ hjj, dotProduct_comm, sub_self]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.affineHullBasis_spec (P : HPolytope (Vec ℝ n)) (c : Vec ℝ n)
    (hc : c ∈ P.construct) {ε φ : ℝ} (hε : 0 ≤ ε) (hεφ : ε < φ)
    (xiter : (r : ℕ) → (Fin r → Vec ℝ n) → Vec ℝ n)
    (hfeas : ∀ r B, (∀ i, B i ⬝ᵥ xiter r B = 0) ∧
      ∃ v ∈ Submodule.span ℝ (Set.range B), c + xiter r B + v ∈ P.construct)
    (hopt : ∀ r (B : Fin r → Vec ℝ n) (x : Vec ℝ n), (∀ i, B i ⬝ᵥ x = 0) →
      (∃ v ∈ Submodule.span ℝ (Set.range B), c + x + v ∈ P.construct) →
        min ‖x‖ φ ≤ ‖xiter r B‖) :
    (∀ i j, i ≠ j → (HPolytope.affineHullBasis ε xiter n 0 Fin.elim0).2 i ⬝ᵥ
        (HPolytope.affineHullBasis ε xiter n 0 Fin.elim0).2 j = 0) ∧
      (∀ i, (HPolytope.affineHullBasis ε xiter n 0 Fin.elim0).2 i ≠ 0) ∧
      (∀ i, (HPolytope.affineHullBasis ε xiter n 0 Fin.elim0).2 i ∈
        Submodule.span ℝ ((· - c) '' P.construct)) ∧
      ∀ z ∈ P.construct, ∃ v ∈ Submodule.span ℝ
        (Set.range (HPolytope.affineHullBasis ε xiter n 0 Fin.elim0).2),
          ‖z - c - v‖ ≤ ε := by -- --- PROOF ---
  set S := Submodule.span ℝ ((· - c) '' P.construct) with hS
  -- the loop, from any state of the invariant with `r + fuel = n` steps in all
  suffices key : ∀ fuel r (B : Fin r → Vec ℝ n), aux_Inv S r B → r + fuel = n →
      aux_Inv S (HPolytope.affineHullBasis ε xiter fuel r B).1
        (HPolytope.affineHullBasis ε xiter fuel r B).2 ∧
      ∀ z ∈ P.construct, ∃ v ∈ Submodule.span ℝ
        (Set.range (HPolytope.affineHullBasis ε xiter fuel r B).2), ‖z - c - v‖ ≤ ε by
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := key n 0 Fin.elim0
      ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩ (zero_add n)
    exact ⟨h1, h2, h3, h4⟩
  intro fuel
  induction fuel with
  -- `n` orthogonal nonzero columns span everything
  | zero =>
    intro r B hinv hr
    rw [add_zero] at hr
    subst hr
    refine ⟨hinv, fun z _ => ⟨z - c, ?_, by rw [sub_self, norm_zero]; exact hε⟩⟩
    have htop := (aux_linearIndependent hinv.1 hinv.2.1).span_eq_top_of_card_eq_finrank'
      (by rw [Fintype.card_fin, Module.finrank_fin_fun])
    show z - c ∈ Submodule.span ℝ (Set.range B)
    rw [htop]
    exact Submodule.mem_top
  | succ fuel ih =>
    intro r B hinv hr
    obtain ⟨hperp, v, hv, hmem⟩ := hfeas r B
    have hdef : HPolytope.affineHullBasis ε xiter (fuel + 1) r B = if ‖xiter r B‖ ≤ ε then ⟨r, B⟩
        else HPolytope.affineHullBasis ε xiter fuel (r + 1)
          (Fin.snoc (α := fun _ => Vec ℝ n) B (xiter r B)) := rfl
    rw [hdef]
    by_cases hsmall : ‖xiter r B‖ ≤ ε
    -- stop: the perpendicular part of any `z - c` is a candidate, so it is short
    · rw [if_pos hsmall]
      refine ⟨hinv, fun z hz => ?_⟩
      obtain ⟨hp, hperp'⟩ := aux_proj hinv.1 hinv.2.1 (z - c)
      refine ⟨_, hp, ?_⟩
      have hcand := hopt r B (z - c - ∑ i, ((z - c) ⬝ᵥ B i / B i ⬝ᵥ B i) • B i) hperp'
        ⟨_, hp, by convert hz using 1; abel⟩
      rcases min_choice ‖z - c - ∑ i, ((z - c) ⬝ᵥ B i / B i ⬝ᵥ B i) • B i‖ φ with hm | hm
      · rw [hm] at hcand
        linarith
      · rw [hm] at hcand
        linarith
    -- append: still orthogonal, nonzero, and in the span of `P - c`
    · rw [if_neg hsmall]
      have hx0 : xiter r B ≠ 0 := fun h => hsmall (by rw [h, norm_zero]; exact hε)
      have hBS : Submodule.span ℝ (Set.range B) ≤ S :=
        Submodule.span_le.mpr (Set.range_subset_iff.mpr hinv.2.2)
      -- `x = (c + x + v - c) - v`, `v` in the span of the old columns
      have hxS : xiter r B ∈ S := by
        have h1 : c + xiter r B + v - c ∈ S := Submodule.subset_span ⟨_, hmem, rfl⟩
        have h2 : xiter r B = (c + xiter r B + v - c) - v := by abel
        rw [h2]
        exact S.sub_mem h1 (hBS hv)
      -- the new column is perpendicular to the old ones, which keep their properties
      refine ih (r + 1) _ ⟨fun i j hij => ?_, fun i => ?_, fun i => ?_⟩ (by omega)
      -- orthogonality, case by case on which index is the new one
      · induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => exact absurd rfl hij
          | cast j =>
            rw [Fin.snoc_last, Fin.snoc_castSucc, dotProduct_comm]
            exact hperp j
        | cast i =>
          induction j using Fin.lastCases with
          | last =>
            rw [Fin.snoc_last, Fin.snoc_castSucc]
            exact hperp i
          | cast j =>
            rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
            exact hinv.1 i j fun h => hij (by rw [h])
      -- nonzero, then in the span of `P - c`
      · induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last]; exact hx0
        | cast i => rw [Fin.snoc_castSucc]; exact hinv.2.1 i
      · induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last]; exact hxS
        | cast i => rw [Fin.snoc_castSucc]; exact hinv.2.2 i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
