module

public import CORALean.ContSet.SpectraShadow.Real.Operations.Inter
public import CORALean.ContSet.SpectraShadow.Real.Theorems.EqBlockSum
public import CORALean.ContSet.SpectraShadow.Real.Theorems.PlusExact

@[expose] public section

/-!
# `SpectraShadow.inter` is exactly the intersection

The inequality of `inter` is `plus`'s with one more diagonal block, `diag e ⊕ diag (-e)`, which is
positive semidefinite exactly when every entry of `e` is both nonnegative and nonpositive: `e = 0`.
So a point is described when the two sets' variables, read off the halves of `β`, give the same
point.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `inter`'s inequality: `plus`'s, and the diagonal block at the difference of the two points. -/
theorem SpectraShadow.aux_lmi_inter (S₁ S₂ : SpectraShadow (Vec ℝ n))
    (β : Fin (S₁.m + S₂.m) → ℝ) : -- --- CONCL ---
    (S₁.inter S₂).A₀ + ∑ i : Fin (S₁.inter S₂).m, β i • (S₁.inter S₂).A i
      = blockDiag 0 ((S₁.plus S₂).A₀ + ∑ i : Fin (S₁.plus S₂).m, β i • (S₁.plus S₂).A i)
        (blockDiag 0
          (diagonal ((S₁.c - S₂.c) + ∑ i, β (Fin.castAdd S₂.m i) • S₁.G i
            - ∑ j, β (Fin.natAdd S₁.m j) • S₂.G j))
          (diagonal (-((S₁.c - S₂.c) + ∑ i, β (Fin.castAdd S₂.m i) • S₁.G i
            - ∑ j, β (Fin.natAdd S₁.m j) • S₂.G j)))) := by -- --- PROOF ---
  set G'' : Fin (S₁.m + S₂.m) → Vec ℝ n := Fin.append S₁.G (fun j => - S₂.G j) with hG
  -- the second blocks' variables carry `-G₂`, so the sum of generators is a difference
  have hsum : ∑ i, β i • G'' i
      = ∑ i, β (Fin.castAdd S₂.m i) • S₁.G i - ∑ j, β (Fin.natAdd S₁.m j) • S₂.G j := by
    rw [Fin.sum_univ_add]
    simp [hG, sub_eq_add_neg, Finset.sum_neg_distrib]
  -- the inequality at the level of the blocks, which `inter` unfolds to
  have key : blockDiag 0 (S₁.plus S₂).A₀
      (blockDiag 0 (diagonal (S₁.c - S₂.c)) (diagonal (-(S₁.c - S₂.c))))
      + ∑ i : Fin (S₁.m + S₂.m), β i • blockDiag 0 ((S₁.plus S₂).A i)
        (blockDiag 0 (diagonal (G'' i)) (diagonal (-G'' i)))
      = blockDiag 0 ((S₁.plus S₂).A₀ + ∑ i : Fin (S₁.plus S₂).m, β i • (S₁.plus S₂).A i)
        (blockDiag 0
          (diagonal ((S₁.c - S₂.c) + ∑ i, β (Fin.castAdd S₂.m i) • S₁.G i
            - ∑ j, β (Fin.natAdd S₁.m j) • S₂.G j))
          (diagonal (-((S₁.c - S₂.c) + ∑ i, β (Fin.castAdd S₂.m i) • S₁.G i
            - ∑ j, β (Fin.natAdd S₁.m j) • S₂.G j)))) := by
    -- a sum of block-diagonal terms is the block-diagonal of the two sums
    have hcomb : ∀ {a b : ℕ} (X : Fin (S₁.m + S₂.m) → Mat ℝ a a)
        (Y : Fin (S₁.m + S₂.m) → Mat ℝ b b),
        ∑ i, β i • blockDiag 0 (X i) (Y i) = blockDiag 0 (∑ i, β i • X i) (∑ i, β i • Y i) := by
      intro a b X Y
      simp_rw [← blockDiag_smul]
      rw [← blockDiag_sum]
    -- the first block is `plus`'s, the second is the diagonal block at the summed vector
    rw [hcomb, ← blockDiag_add, SpectraShadow.eq_block_sum, hsum]
    congr 1
    rw [← blockDiag_add]
    congr 1 <;> (ext j k; by_cases hjk : j = k <;> simp [hjk]; ring)
  exact key

/-- A point is described exactly when both halves of `β` are in their sets' inequalities and the
two points they read off agree. -/
theorem SpectraShadow.aux_posSemidef_inter_iff (S₁ S₂ : SpectraShadow (Vec ℝ n))
    (β : Fin (S₁.m + S₂.m) → ℝ) : -- --- CONCL ---
    ((S₁.inter S₂).A₀ + ∑ i : Fin (S₁.inter S₂).m, β i • (S₁.inter S₂).A i).PosSemidef
      ↔ ((S₁.A₀ + ∑ i, β (Fin.castAdd S₂.m i) • S₁.A i).PosSemidef
          ∧ (S₂.A₀ + ∑ j, β (Fin.natAdd S₁.m j) • S₂.A j).PosSemidef)
        ∧ S₁.c + ∑ i, β (Fin.castAdd S₂.m i) • S₁.G i
          = S₂.c + ∑ j, β (Fin.natAdd S₁.m j) • S₂.G j := by -- --- PROOF ---
  rw [SpectraShadow.aux_lmi_inter]
  refine ((posSemidef_blockDiag_iff _ _).trans (and_congr
    (SpectraShadow.posSemidef_plus_iff S₁ S₂ β) (posSemidef_blockDiag_iff _ _))).trans ?_
  rw [posSemidef_diagonal_iff, posSemidef_diagonal_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨h₁, h₂⟩
    ext j
    have a := h₁ j
    have b := h₂ j
    simp only [Pi.neg_apply, Pi.sub_apply, Pi.add_apply] at a b
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
    linarith
  · intro h
    have : (S₁.c - S₂.c) + ∑ i, β (Fin.castAdd S₂.m i) • S₁.G i
        - ∑ j, β (Fin.natAdd S₁.m j) • S₂.G j = 0 := by
      rw [sub_eq_zero, sub_add_eq_add_sub, h, add_sub_cancel_left]
    rw [this]
    simp

/-- The point of `inter` is `S₁`'s, read at the first half of the variables. -/
theorem SpectraShadow.aux_gen_inter (S₁ S₂ : SpectraShadow (Vec ℝ n))
    (β : Fin (S₁.m + S₂.m) → ℝ) :
    (S₁.inter S₂).c + ∑ i : Fin (S₁.inter S₂).m, β i • (S₁.inter S₂).G i
      = S₁.c + ∑ i, β (Fin.castAdd S₂.m i) • S₁.G i := by -- --- PROOF ---
  have h : ∑ i : Fin (S₁.inter S₂).m, β i • (S₁.inter S₂).G i
      = ∑ i, β (Fin.castAdd S₂.m i) • S₁.G i + ∑ j, β (Fin.natAdd S₁.m j) • (0 : Vec ℝ n) :=
    Fin.sum_univ_add (fun i => β i • (Fin.append S₁.G (0 : Fin S₂.m → Vec ℝ n) i))
      |>.trans (by simp)
  rw [h]
  simp [SpectraShadow.inter]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.inter_exact (S₁ S₂ : SpectraShadow (Vec ℝ n)) :
    S₁.construct ∩ S₂.construct = (S₁.inter S₂).construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨⟨β₁, h₁, hx₁⟩, ⟨β₂, h₂, hx₂⟩⟩
    refine ⟨Fin.append β₁ β₂, (SpectraShadow.aux_posSemidef_inter_iff S₁ S₂ _).mpr ⟨?_, ?_⟩, ?_⟩
    · simpa using ⟨h₁, h₂⟩
    · simpa using hx₁.symm.trans hx₂
    · rw [hx₁, SpectraShadow.aux_gen_inter]
      simp
  · rintro x ⟨β, hβ, hx⟩
    obtain ⟨⟨h₁, h₂⟩, he⟩ := (SpectraShadow.aux_posSemidef_inter_iff S₁ S₂ β).mp hβ
    have hx₁ : x = S₁.c + ∑ i, β (Fin.castAdd S₂.m i) • S₁.G i := by
      rw [hx, SpectraShadow.aux_gen_inter]
    exact ⟨⟨_, h₁, hx₁⟩, ⟨_, h₂, hx₁.trans he⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
