module

public import CORALean.Global.CoeffNormHalfGadgetH
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set

@[expose] public section

/-!
# The circumbody of the reduction: a zonotope with cross-polytope slices

[1, Lemma 25]: for `Ẑ = {H β | ‖β‖_∞ ≤ 1, β ≥ 0}` and `H` of [1, Eq. 63],
`Ẑ = Z(½H, n e_{n+1})`; its slice at a height `ρ ∈ [0, 1]` is `(ρB₁) × {ρ}` (Eq. 64); and
`B₁ × [1, 2n - 1] ⊂ Ẑ`. The first is `β = (β' + 1) / 2`; the other two read the membership off
the closed-form norm of `Z(½H)` (`coeffNorm_half_gadgetH`): `(y, t) ∈ Ẑ` iff `‖y‖_∞ ≤ 1` and
`‖y‖₁ + |t - n| ≤ n`. The paper's `n > 1` is `2 ≤ n`; the proof uses `1 ≤ n` only.

## Inputs
* none

## Hypotheses
* `hn` – the dimension is at least two

## Conclusion
* the circumbody is a zonotope with cross-polytope slices and contains the stated box

## References

* [1] [A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control,
      2025.](../../../references/2025/kulmburg-tac-approximability-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A coefficient pair is in the unit ball iff every entry is in `[-1, 1]`. -/
private theorem aux_norm_le_one_iff (β : Vec ℝ n × Vec ℝ n) :
    ‖β‖ ≤ 1 ↔ ∀ i, |β.1 i| ≤ 1 ∧ |β.2 i| ≤ 1 := by
  rw [Prod.norm_def, max_le_iff, pi_norm_le_iff_of_nonneg zero_le_one,
    pi_norm_le_iff_of_nonneg zero_le_one]
  simp only [Real.norm_eq_abs]
  exact ⟨fun ⟨h1, h2⟩ i => ⟨h1 i, h2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- The supremum norm is below the `1`-norm. -/
private theorem aux_norm_le_sum_abs (y : Vec ℝ n) : ‖y‖ ≤ ∑ i, |y i| :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).mpr fun i =>
    (Real.norm_eq_abs _).trans_le
      (Finset.single_le_sum (f := fun i => |y i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))

/-- Membership in `Z(½H, n e_{n+1})` through the closed-form norm. -/
private theorem aux_mem_iff (hn : 1 ≤ n) (y : Vec ℝ n) (t : ℝ) : -- --- CONCL ---
    (∃ β : Vec ℝ n × Vec ℝ n, ‖β‖ ≤ 1 ∧ (y, t) = ((0 : Vec ℝ n), (n : ℝ)) +
        ((1 / 2 : ℝ) • gadgetH n) β) ↔
      ‖y‖ ≤ 1 ∧ ∑ i, |y i| + |t - n| ≤ n := by -- --- PROOF ---
  obtain ⟨hsurj, hnorm⟩ := coeffNorm_half_gadgetH hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have key := coeffNorm_le_iff ((1 / 2 : ℝ) • gadgetH n) (hsurj (y, t - n)) (r := 1)
  rw [hnorm, max_le_iff, div_le_one hnpos] at key
  rw [key]
  constructor
  · rintro ⟨β, hβ, he⟩
    refine ⟨β, ?_, hβ⟩
    rw [Prod.ext_iff] at he ⊢
    simp only [Prod.fst_add, Prod.snd_add, zero_add] at he ⊢
    exact ⟨he.1.symm, by linarith [he.2]⟩
  · rintro ⟨β, he, hβ⟩
    refine ⟨β, hβ, ?_⟩
    rw [Prod.ext_iff] at he ⊢
    simp only [Prod.fst_add, Prod.snd_add, zero_add] at he ⊢
    exact ⟨he.1.symm, by linarith [he.2]⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem gadget_zonotope (hn : 2 ≤ n) : -- --- CONCL ---
    let Zh := {x : Vec ℝ n × ℝ | ∃ β : Vec ℝ n × Vec ℝ n,
      ‖β‖ ≤ 1 ∧ (∀ i, 0 ≤ β.1 i ∧ 0 ≤ β.2 i) ∧ x = gadgetH n β}
    Zh = {x | ∃ β : Vec ℝ n × Vec ℝ n, ‖β‖ ≤ 1 ∧
        x = ((0 : Vec ℝ n), (n : ℝ)) + ((1 / 2 : ℝ) • gadgetH n) β} ∧
      (∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
        {x : Vec ℝ n × ℝ | x.2 = ρ} ∩ Zh =
          (fun y => (y, ρ)) '' (ρ • {y : Vec ℝ n | ∑ i, |y i| ≤ 1})) ∧
      {x : Vec ℝ n × ℝ | ∑ i, |x.1 i| ≤ 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 2 * n - 1} ⊆ Zh := by -- --- PROOF ---
  intro Zh
  have hn1 : 1 ≤ n := by omega
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  -- `β ≥ 0` in the unit ball is `β' = 2β - 1` in the unit ball, and `Hβ = n e_{n+1} + ½Hβ'`
  have hZ : Zh = {x | ∃ β : Vec ℝ n × Vec ℝ n, ‖β‖ ≤ 1 ∧
      x = ((0 : Vec ℝ n), (n : ℝ)) + ((1 / 2 : ℝ) • gadgetH n) β} := by
    have hshift : ∀ β : Vec ℝ n × Vec ℝ n, gadgetH n β = ((0 : Vec ℝ n), (n : ℝ)) +
        ((1 / 2 : ℝ) • gadgetH n) ((2 : ℝ) • β - ((fun _ => 1), (fun _ => 1))) := by
      intro β
      rw [half_gadgetH_apply]
      refine Prod.ext ?_ ?_
      · funext i
        simp only [gadgetH, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_add, Prod.fst_sub,
          Prod.smul_fst, Prod.snd_sub, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
          Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
        ring
      · simp only [gadgetH, LinearMap.coe_mk, AddHom.coe_mk, Prod.snd_add, Prod.fst_sub,
          Prod.smul_fst, Prod.snd_sub, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one, ← Finset.mul_sum]
        ring
    -- both directions through `β' = 2β - 1`
    ext x
    constructor
    · rintro ⟨β, hβ, hpos, rfl⟩
      refine ⟨(2 : ℝ) • β - ((fun _ => 1), (fun _ => 1)), ?_, hshift β⟩
      rw [aux_norm_le_one_iff] at hβ ⊢
      intro i
      obtain ⟨h1, h2⟩ := hβ i
      obtain ⟨p1, p2⟩ := hpos i
      simp only [Prod.fst_sub, Prod.smul_fst, Prod.snd_sub, Prod.smul_snd, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [abs_of_nonneg p1] at h1; rw [abs_of_nonneg p2] at h2
      exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    -- and back through `β = (β' + 1) / 2`
    · rintro ⟨β', hβ', rfl⟩
      set β : Vec ℝ n × Vec ℝ n := (1 / 2 : ℝ) • (β' + ((fun _ => 1), (fun _ => 1))) with hβdef
      have hβ'eq : β' = (2 : ℝ) • β - ((fun _ => 1), (fun _ => 1)) := by
        rw [hβdef, smul_smul]; norm_num
      rw [aux_norm_le_one_iff] at hβ'
      refine ⟨β, (aux_norm_le_one_iff β).mpr fun i => ?_, fun i => ?_, by rw [hshift, ← hβ'eq]⟩
      · obtain ⟨h1, h2⟩ := hβ' i
        obtain ⟨h1l, h1u⟩ := abs_le.mp h1
        obtain ⟨h2l, h2u⟩ := abs_le.mp h2
        simp only [hβdef, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
          Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
      · obtain ⟨h1, h2⟩ := hβ' i
        obtain ⟨h1l, -⟩ := abs_le.mp h1
        obtain ⟨h2l, -⟩ := abs_le.mp h2
        simp only [hβdef, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
          Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        exact ⟨by linarith, by linarith⟩
  refine ⟨hZ, fun ρ hρ0 hρ1 => ?_, ?_⟩
  · -- the slice: `‖y‖₁ + n - ρ ≤ n`, which already gives `‖y‖_∞ ≤ 1`
    ext ⟨y, t⟩
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]
    rw [hZ, Set.mem_setOf_eq, aux_mem_iff hn1]
    -- `ρ B₁` is the `1`-norm ball of radius `ρ`, `{0}` at `ρ = 0`
    have hball : y ∈ ρ • {y : Vec ℝ n | ∑ i, |y i| ≤ 1} ↔ ∑ i, |y i| ≤ ρ := by
      rcases hρ0.lt_or_eq with hpos | rfl
      · rw [Set.mem_smul_set]
        constructor
        · rintro ⟨z, hz, rfl⟩
          simp only [Set.mem_setOf_eq] at hz
          simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hpos, ← Finset.mul_sum]
          nlinarith
        · intro hy
          refine ⟨ρ⁻¹ • y, ?_, by rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]⟩
          simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, abs_mul,
            abs_inv, abs_of_pos hpos, ← Finset.mul_sum]
          rw [inv_mul_le_iff₀ hpos]; linarith
      -- `ρ = 0`: the zero vector alone
      · rw [Set.zero_smul_set ⟨0, by simp⟩, Set.mem_zero]
        constructor
        · rintro rfl; simp
        · intro hy
          funext i
          have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg (y i)).mp
            (le_antisymm hy (Finset.sum_nonneg fun _ _ => abs_nonneg _)) i (Finset.mem_univ i)
          exact abs_eq_zero.mp this
    -- the slice through the closed form, `n - ρ` being `|ρ - n|`
    constructor
    · rintro ⟨rfl, -, hs⟩
      refine ⟨y, hball.mpr ?_, rfl, rfl⟩
      rw [abs_of_nonpos (by linarith)] at hs
      linarith
    · rintro ⟨z, hz, rfl, rfl⟩
      have hs := hball.mp hz
      refine ⟨rfl, (aux_norm_le_sum_abs z).trans (hs.trans hρ1), ?_⟩
      rw [abs_of_nonpos (by linarith)]
      linarith
  · -- the tube: `‖y‖₁ ≤ 1` and `|t - n| ≤ n - 1`
    rintro ⟨y, t⟩ ⟨hy, ht1, ht2⟩
    rw [hZ, Set.mem_setOf_eq, aux_mem_iff hn1]
    refine ⟨(aux_norm_le_sum_abs y).trans hy, ?_⟩
    have : |t - n| ≤ n - 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
