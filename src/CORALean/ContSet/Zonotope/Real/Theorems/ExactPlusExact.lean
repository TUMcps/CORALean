module

public import CORALean.ContSet.Zonotope.Real.Operations.ExactPlus
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# `exactPlus` is the sum over shared coefficients

`construct (exactPlus Z₁ Z₂ k)` is the set of sums `x₁ + x₂` of a point of `Z₁` (coefficients `β`)
and a point of `Z₂` (coefficients `γ`) whose coefficients agree on the first `k` generators the
two have in common. Equality, not enclosure: dropping the agreement is `plus`, of which this is a
subset. The proof regroups the coefficients of the result, `[shared | rest of Z₁ | rest of Z₂]`,
into `β` and `γ` and back.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- `Fin.sum_univ_add` for a generator count written as `m + d` only by a proof. -/
theorem Zonotope.aux_sum_split {h m d : ℕ} (hd : h = m + d) (f : Fin h → α) :
    ∑ j, f j = ∑ i : Fin m, f ⟨i, by have := i.2; omega⟩
      + ∑ i : Fin d, f ⟨m + i, by have := i.2; omega⟩ := by
  subst hd
  exact Fin.sum_univ_add f

theorem Zonotope.aux_min_le_left (a b k : ℕ) : min (min a b) k ≤ a := by omega

theorem Zonotope.aux_min_le_right (a b k : ℕ) : min (min a b) k ≤ b := by omega

/-- A sum over three appended blocks, one block at a time. -/
theorem Zonotope.aux_sum_append3 {a b c : ℕ} (δ : Fin (a + b + c) → ℝ) (A : Fin a → α)
    (B : Fin b → α) (C : Fin c → α) : -- --- STMT ---
    ∑ j, δ j • Fin.append (Fin.append A B) C j =
      ∑ i, δ (Fin.castAdd c (Fin.castAdd b i)) • A i
      + ∑ i, δ (Fin.castAdd c (Fin.natAdd a i)) • B i
      + ∑ i, δ (Fin.natAdd (a + b) i) • C i := by -- --- PROOF ---
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right, add_assoc]

/-- The generator sum of `exactPlus`, one block at a time. -/
theorem Zonotope.aux_sum_exactPlus (Z₁ Z₂ : Zonotope α) (k : ℕ)
    (δ : Fin (Z₁.exactPlus Z₂ k).h → ℝ) : -- --- STMT ---
    ∑ j, δ j • (Z₁.exactPlus Z₂ k).G j =
      ∑ i : Fin (min (min Z₁.h Z₂.h) k),
        δ (Fin.castAdd _ (Fin.castAdd _ i)) •
          (Z₁.G (Fin.castLE (Zonotope.aux_min_le_left _ _ _) i)
            + Z₂.G (Fin.castLE (Zonotope.aux_min_le_right _ _ _) i))
      + ∑ i : Fin (Z₁.h - min (min Z₁.h Z₂.h) k),
        δ (Fin.castAdd _ (Fin.natAdd _ i)) •
          Z₁.G ⟨min (min Z₁.h Z₂.h) k + i, by have := i.2; omega⟩
      + ∑ i : Fin (Z₂.h - min (min Z₁.h Z₂.h) k),
        δ (Fin.natAdd _ i) •
          Z₂.G ⟨min (min Z₁.h Z₂.h) k + i, by have := i.2; omega⟩ := by -- --- PROOF ---
  have := Zonotope.aux_sum_append3 (a := min (min Z₁.h Z₂.h) k) (b := Z₁.h - min (min Z₁.h Z₂.h) k)
    (c := Z₂.h - min (min Z₁.h Z₂.h) k) δ
    (fun i => Z₁.G (Fin.castLE (Zonotope.aux_min_le_left _ _ _) i)
      + Z₂.G (Fin.castLE (Zonotope.aux_min_le_right _ _ _) i))
    (fun i => Z₁.G ⟨min (min Z₁.h Z₂.h) k + i, by have := i.2; omega⟩)
    (fun i => Z₂.G ⟨min (min Z₁.h Z₂.h) k + i, by have := i.2; omega⟩)
  exact this


theorem Zonotope.aux_abs_append3 {a b c : ℕ} {A : Fin a → ℝ} {B : Fin b → ℝ} {C : Fin c → ℝ}
    (hA : ∀ i, |A i| ≤ 1) (hB : ∀ i, |B i| ≤ 1) (hC : ∀ i, |C i| ≤ 1) :
    ∀ j, |Fin.append (Fin.append A B) C j| ≤ 1 := by -- --- PROOF ---
  intro j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Fin.append_left]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]; exact hA j
    · rw [Fin.append_right]; exact hB j
  · rw [Fin.append_right]; exact hC j


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.exactPlus_construct (Z₁ Z₂ : Zonotope α) (k : ℕ) : -- --- STMT ---
    (Z₁.exactPlus Z₂ k).construct =
      {x | ∃ (β : Fin Z₁.h → ℝ) (γ : Fin Z₂.h → ℝ), (∀ j, |β j| ≤ 1) ∧ (∀ j, |γ j| ≤ 1) ∧
        (∀ (j₁ : Fin Z₁.h) (j₂ : Fin Z₂.h), (j₁ : ℕ) = j₂ → (j₁ : ℕ) < k → β j₁ = γ j₂) ∧
        x = (Z₁.c + ∑ j, β j • Z₁.G j) + (Z₂.c + ∑ j, γ j • Z₂.G j)} := by -- --- PROOF ---
  ext x
  constructor
  · -- from the result's coefficients `δ`, read off `β` and `γ` block by block
    rintro ⟨δ, hδ, rfl⟩
    let β : Fin Z₁.h → ℝ := fun j =>
      if hj : (j : ℕ) < min (min Z₁.h Z₂.h) k then
        δ (Fin.castAdd _ (Fin.castAdd _ ⟨j, hj⟩))
      else δ (Fin.castAdd _ (Fin.natAdd _ ⟨j - min (min Z₁.h Z₂.h) k, by have := j.2; omega⟩))
    let γ : Fin Z₂.h → ℝ := fun j =>
      if hj : (j : ℕ) < min (min Z₁.h Z₂.h) k then
        δ (Fin.castAdd _ (Fin.castAdd _ ⟨j, hj⟩))
      else δ (Fin.natAdd _ ⟨j - min (min Z₁.h Z₂.h) k, by have := j.2; omega⟩)
    refine ⟨β, γ, fun j => ?_, fun j => ?_, fun j₁ j₂ h₁₂ hk => ?_, ?_⟩
    · simp only [β]; split_ifs <;> exact hδ _
    · simp only [γ]; split_ifs <;> exact hδ _
    · have hm : (j₁ : ℕ) < min (min Z₁.h Z₂.h) k := by have := j₁.2; have := j₂.2; omega
      have hm' : (j₂ : ℕ) < min (min Z₁.h Z₂.h) k := h₁₂ ▸ hm
      simp only [β, γ, dif_pos hm, dif_pos hm']
      have : (⟨j₁, hm⟩ : Fin (min (min Z₁.h Z₂.h) k)) = ⟨j₂, hm'⟩ := Fin.ext h₁₂
      rw [this]
    · -- the sum is the three blocks of `aux_sum_exactPlus`, regrouped per operand
      have h1 := Zonotope.aux_sum_split (f := fun j => β j • Z₁.G j)
        (Nat.add_sub_cancel' (Zonotope.aux_min_le_left Z₁.h Z₂.h k)).symm
      have h2 := Zonotope.aux_sum_split (f := fun j => γ j • Z₂.G j)
        (Nat.add_sub_cancel' (Zonotope.aux_min_le_right Z₁.h Z₂.h k)).symm
      rw [Zonotope.aux_sum_exactPlus, h1, h2]
      -- below `m` a coefficient of `Z₁` or `Z₂` is the shared one, above it the rest block's
      have hβlo : ∀ (i : Fin (min (min Z₁.h Z₂.h) k)) (hi : (i : ℕ) < Z₁.h),
          β ⟨i, hi⟩ = δ (Fin.castAdd _ (Fin.castAdd _ i)) := fun i hi => dif_pos i.2
      have hβhi : ∀ (b : Fin (Z₁.h - min (min Z₁.h Z₂.h) k))
          (hb : min (min Z₁.h Z₂.h) k + (b : ℕ) < Z₁.h),
          β ⟨min (min Z₁.h Z₂.h) k + b, hb⟩ = δ (Fin.castAdd _ (Fin.natAdd _ b)) := by
        intro b hb
        show dite _ _ _ = _
        rw [dif_neg (by simp only [not_lt]; exact Nat.le_add_right _ _)]
        exact congrArg δ (congrArg _ (congrArg _ (Fin.ext (by simp))))
      have hγlo : ∀ (i : Fin (min (min Z₁.h Z₂.h) k)) (hi : (i : ℕ) < Z₂.h),
          γ ⟨i, hi⟩ = δ (Fin.castAdd _ (Fin.castAdd _ i)) := fun i hi => dif_pos i.2
      have hγhi : ∀ (b : Fin (Z₂.h - min (min Z₁.h Z₂.h) k))
          (hb : min (min Z₁.h Z₂.h) k + (b : ℕ) < Z₂.h),
          γ ⟨min (min Z₁.h Z₂.h) k + b, hb⟩ = δ (Fin.natAdd _ b) := by
        intro b hb
        show dite _ _ _ = _
        rw [dif_neg (by simp only [not_lt]; exact Nat.le_add_right _ _)]
        exact congrArg δ (congrArg _ (Fin.ext (by simp)))
      -- both sides are now the same blocks, in another order
      simp only [hβlo, hβhi, hγlo, hγhi, smul_add, Finset.sum_add_distrib]
      show Z₁.c + Z₂.c + _ = _
      simp only [Fin.castLE]
      abel
  · -- from `β` and `γ`, stack them as `[shared | rest of Z₁ | rest of Z₂]`
    rintro ⟨β, γ, hβ, hγ, hs, rfl⟩
    let δ : Fin (Z₁.exactPlus Z₂ k).h → ℝ :=
      Fin.append
        (Fin.append (fun i : Fin (min (min Z₁.h Z₂.h) k) =>
            β (Fin.castLE (Zonotope.aux_min_le_left _ _ _) i))
          (fun b : Fin (Z₁.h - min (min Z₁.h Z₂.h) k) =>
            β ⟨min (min Z₁.h Z₂.h) k + b, by have := b.2; omega⟩))
        (fun c : Fin (Z₂.h - min (min Z₁.h Z₂.h) k) =>
          γ ⟨min (min Z₁.h Z₂.h) k + c, by have := c.2; omega⟩)
    -- the stacked coefficients are in the cube, and shared ones agree by `hs`
    refine ⟨δ, Zonotope.aux_abs_append3 (fun i => hβ _) (fun i => hβ _) (fun i => hγ _), ?_⟩
    have h1 := Zonotope.aux_sum_split (f := fun j => β j • Z₁.G j)
      (Nat.add_sub_cancel' (Zonotope.aux_min_le_left Z₁.h Z₂.h k)).symm
    have h2 := Zonotope.aux_sum_split (f := fun j => γ j • Z₂.G j)
      (Nat.add_sub_cancel' (Zonotope.aux_min_le_right Z₁.h Z₂.h k)).symm
    have hsh : ∀ (i : Fin (min (min Z₁.h Z₂.h) k)) (h₂ : (i : ℕ) < Z₂.h),
        γ ⟨i, h₂⟩ = β ⟨i, lt_of_lt_of_le i.2 (Zonotope.aux_min_le_left _ _ _)⟩ := fun i h₂ =>
      (hs ⟨i, lt_of_lt_of_le i.2 (Zonotope.aux_min_le_left _ _ _)⟩ ⟨i, h₂⟩ rfl
        (by show (i : ℕ) < k; have := i.2; omega)).symm
    rw [Zonotope.aux_sum_exactPlus, h1, h2]
    -- unfold the stacked coefficients block by block and compare
    simp only [δ, Fin.append_left, Fin.append_right, hsh, smul_add, Finset.sum_add_distrib,
      Fin.castLE]
    show _ = Z₁.c + Z₂.c + _
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
