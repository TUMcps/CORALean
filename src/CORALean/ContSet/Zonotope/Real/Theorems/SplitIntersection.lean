module

public import CORALean.ContSet.Zonotope.Real.Operations.Split
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.Zonotope.Real.Theorems.SumSmulUpdate
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# What a split costs: where the two halves overlap

`Z₁ ∩ Z₂` is `Z` with the `j`-th generator gone [1, Prop. 3.8], written here as
that generator set to `0` — the same set, and it keeps the generator index a
`Fin Z.h`, which dropping a column would not.

`⊇` is a coefficient each way, `±1` on the halved generator. `⊆` is not: a point
of both halves is `c + s·g + r₁` with `s ≤ 0` and `c + s'·g + r₂` with `s' ≥ 0`,
and the two reaches `r₁`, `r₂` need not agree, so the point is read as a convex
combination of `c + r₁` and `c + r₂` at `s'/(s' - s)`, which is where it takes
`convex_construct`.

The thesis argues instead from `(-g/2; g/2) ∩ (g/2; g/2) = {0}` together with
`A + (B ∩ C) = (A + B) ∩ (A + C)`. That identity is false for sets: at
`A = [0,1]`, `B = {0}`, `C = {1}` in ℝ the left side is empty and the right side
is `{1}`, and convexity is what the missing step actually needs.

It first appeared as [2, Prop. 3], whose proof takes the same step.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
* [2] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The two halves of a split meet in the zonotope the split generator is
dropped from, exactly. -/
theorem Zonotope.split_intersection (Z : Zonotope α) (j : Fin Z.h) :
    (Z.split j).1.construct ∩ (Z.split j).2.construct
      = ({Z with G := Function.update Z.G j 0} : Zonotope α).construct := by -- --- PROOF ---
  -- all three sets read over `Fin Z.h`, which they are only up to unfolding
  have h₁ : (Z.split j).1.construct = {x | ∃ β : Fin Z.h → ℝ, (∀ k, |β k| ≤ 1) ∧
      x = Z.c - (2 : ℝ)⁻¹ • Z.G j
        + ∑ k, β k • Function.update Z.G j ((2 : ℝ)⁻¹ • Z.G j) k} := rfl
  have h₂ : (Z.split j).2.construct = {x | ∃ β : Fin Z.h → ℝ, (∀ k, |β k| ≤ 1) ∧
      x = Z.c + (2 : ℝ)⁻¹ • Z.G j
        + ∑ k, β k • Function.update Z.G j ((2 : ℝ)⁻¹ • Z.G j) k} := rfl
  have hO : ({Z with G := Function.update Z.G j 0} : Zonotope α).construct
      = {x | ∃ δ : Fin Z.h → ℝ, (∀ k, |δ k| ≤ 1) ∧
          x = Z.c + ∑ k, δ k • Function.update Z.G j (0 : α) k} := rfl
  -- the overlap is still a zonotope, so it is still convex
  have hconv : Convex ℝ {x : α | ∃ δ : Fin Z.h → ℝ, (∀ k, |δ k| ≤ 1) ∧
      x = Z.c + ∑ k, δ k • Function.update Z.G j (0 : α) k} := by
    rw [← hO]
    exact Zonotope.convex_construct _
  have hsum : ∀ (β : Fin Z.h → ℝ) (a : α),
      ∑ k, β k • Function.update Z.G j a k
        = β j • a + ∑ k ∈ Finset.univ.erase j, β k • Z.G k := fun β a => by
    have h := Zonotope.sum_smul_update β Z.G j (β j) a
    rwa [Function.update_eq_self] at h
  -- a reach over every generator but the `j`-th is a point of the overlap
  have hmem : ∀ (δ : Fin Z.h → ℝ), (∀ k, |δ k| ≤ 1) →
      Z.c + ∑ k ∈ Finset.univ.erase j, δ k • Z.G k
        ∈ {x : α | ∃ δ : Fin Z.h → ℝ, (∀ k, |δ k| ≤ 1) ∧
            x = Z.c + ∑ k, δ k • Function.update Z.G j (0 : α) k} :=
    fun δ hδ => ⟨δ, hδ, by rw [hsum δ 0, smul_zero, zero_add]⟩
  rw [h₁, h₂, hO]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨β, hβ, hx₁⟩, β', hβ', hx₂⟩
    rw [hsum β ((2 : ℝ)⁻¹ • Z.G j), smul_smul] at hx₁
    rw [hsum β' ((2 : ℝ)⁻¹ • Z.G j), smul_smul] at hx₂
    have hp₁ := hmem β hβ
    have hp₂ := hmem β' hβ'
    -- each half offers `x` as one point of the overlap plus a multiple of `g`
    have hP₁ : Z.c + ∑ k ∈ Finset.univ.erase j, β k • Z.G k
        = x - (β j * 2⁻¹ - 2⁻¹) • Z.G j := by
      rw [hx₁, sub_smul]; abel
    have hP₂ : Z.c + ∑ k ∈ Finset.univ.erase j, β' k • Z.G k
        = x - (β' j * 2⁻¹ + 2⁻¹) • Z.G j := by
      rw [hx₂, add_smul]; abel
    have hb := abs_le.mp (hβ j)
    have hb' := abs_le.mp (hβ' j)
    -- the two multiples straddle zero, which is what makes the combination convex
    have hsle : β j * 2⁻¹ - 2⁻¹ ≤ 0 := by linarith [hb.2]
    have hsge : (0 : ℝ) ≤ β' j * 2⁻¹ + 2⁻¹ := by linarith [hb'.1]
    rcases eq_or_lt_of_le (hsle.trans hsge) with heq | hlt
    · have hz : β j * 2⁻¹ - 2⁻¹ = 0 := by linarith
      rw [hz, zero_smul, sub_zero] at hP₁
      rw [← hP₁]; exact hp₁
    · have hd : (0 : ℝ) < β' j * 2⁻¹ + 2⁻¹ - (β j * 2⁻¹ - 2⁻¹) := by linarith
      set l : ℝ := (β' j * 2⁻¹ + 2⁻¹) / (β' j * 2⁻¹ + 2⁻¹ - (β j * 2⁻¹ - 2⁻¹)) with hl
      have hl0 : (0 : ℝ) ≤ l := div_nonneg hsge hd.le
      have hl1 : l ≤ 1 := (div_le_one hd).mpr (by linarith)
      -- the weight that cancels `g` out of the combination
      have hld : l * (β' j * 2⁻¹ + 2⁻¹ - (β j * 2⁻¹ - 2⁻¹)) = β' j * 2⁻¹ + 2⁻¹ := by
        rw [hl]; exact div_mul_cancel₀ _ (ne_of_gt hd)
      have hzero : l * (β j * 2⁻¹ - 2⁻¹) + (1 - l) * (β' j * 2⁻¹ + 2⁻¹) = 0 := by
        linarith [hld]
      have hone : l + (1 - l) = (1 : ℝ) := by ring
      have hx : l • (Z.c + ∑ k ∈ Finset.univ.erase j, β k • Z.G k)
          + (1 - l) • (Z.c + ∑ k ∈ Finset.univ.erase j, β' k • Z.G k) = x := by
        rw [hP₁, hP₂, smul_sub, smul_sub, smul_smul, smul_smul]
        calc l • x - (l * (β j * 2⁻¹ - 2⁻¹)) • Z.G j
              + ((1 - l) • x - ((1 - l) * (β' j * 2⁻¹ + 2⁻¹)) • Z.G j)
            = (l + (1 - l)) • x
              - (l * (β j * 2⁻¹ - 2⁻¹) + (1 - l) * (β' j * 2⁻¹ + 2⁻¹)) • Z.G j := by
              rw [add_smul, add_smul]; abel
          _ = x := by rw [hone, hzero, one_smul, zero_smul, sub_zero]
      rw [← hx]
      exact hconv hp₁ hp₂ hl0 (by linarith) (by ring)
  -- back: `±1` on the halved generator undoes the centre shift
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨⟨Function.update δ j 1, fun k => ?_, ?_⟩,
      Function.update δ j (-1), fun k => ?_, ?_⟩
    · rcases eq_or_ne k j with rfl | hk
      · rw [Function.update_self]; norm_num
      · rw [Function.update_of_ne hk]; exact hδ k
    · rw [hsum δ 0, Zonotope.sum_smul_update δ Z.G j 1 ((2 : ℝ)⁻¹ • Z.G j),
        smul_zero, zero_add, one_smul]
      abel
    · rcases eq_or_ne k j with rfl | hk
      · rw [Function.update_self]; norm_num
      · rw [Function.update_of_ne hk]; exact hδ k
    · rw [hsum δ 0, Zonotope.sum_smul_update δ Z.G j (-1) ((2 : ℝ)⁻¹ • Z.G j),
        smul_zero, zero_add, neg_one_smul]
      abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
