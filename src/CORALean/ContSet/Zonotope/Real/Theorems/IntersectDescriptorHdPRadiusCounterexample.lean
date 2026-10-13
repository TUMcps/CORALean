import CORALean.ContSet.Zonotope.Real.Operations.IntersectDescriptor
import CORALean.ContSet.Zonotope.Real.Definitions.PRadius
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# The printed P-radius condition does not bound the P-radius

[1, Thm. 2] concludes `ϱ_k ≤ α ϱ_{k-1} + (1 - α) ℓ_d` (its Eq. 21a), `ℓ_d` its Eq. 22, from its
Eq. 19, whose last block row carries `P(NF - ΛCNF + ΛF)` with a single coefficient. The
intersection zonotope [1, Thm. 1] has `(I - ΛC)NF H_d` and `ΛF H_d` as separate generator blocks,
which can add up where Eq. 19 lets them cancel. With `n_x = n_y = n_d = 1`, `E = 0`, `C = 1`,
`T = 0`, `N = 1` (so `TE + NC = I`), `F = H_d = 1`, `A = B = D = 0` (`D(θ) = [D̄ 0]` with no
disturbance, `F = [0 F̄]`), `Λ = 2`, `P = 1/5`, `α = β = 1/2`, `γ = 3` and `X̂_{k-1} = {0}`, Eq. 19
holds (`NF - ΛCNF + ΛF = 1`), so does `I ≼ γ²P` (its Eq. 26), and the zonotope `⟨0, [-1  2]⟩` has
P-radius `9/5`, above `α · 0 + (1 - α)(β · 1 + (1 - β) · 1) = 1/2`. Eq. 20 itself has no solution
(`LinearSysDT.radiusLmi_infeasible`), so the theorem as printed is vacuous; with Eq. 26 for
Eq. 20, as its proof derives, Eq. 21a fails. Splitting the block corrects it
(`intersectDescriptorHd_pRadius_le`).

## References

* [1] Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for
      discrete-time descriptor LPV systems". IEEE Transactions on Automatic Control,
      64(5):2092-2099, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- Eq. 19 at the instance: its form is `x₁²/10 + x₂²/4 + (x₃/2 + 2x₄/5)² + x₄²/25`
theorem Zonotope.aux_pRadiusCounterexample_lmi :
    let T : Mat ℝ 1 1 := 0
    let N : Mat ℝ 1 1 := 1
    let Λ : Mat ℝ 1 1 := fun _ _ => 2
    let A : Mat ℝ 1 1 := 0
    let D : Mat ℝ 1 1 := 0
    let C : Mat ℝ 1 1 := 1
    let F : Mat ℝ 1 1 := 1
    let P : Mat ℝ 1 1 := fun _ _ => 1 / 5
    let α : ℝ := 1 / 2
    let β : ℝ := 1 / 2
    (fromBlocks (fromBlocks (α • P) 0 0
      (fromBlocks (((1 - α) * β) • 1) 0 0 (((1 - α) * (1 - β)) • 1)))
      (fromCols (P * (1 - Λ * C) * T * A) (fromCols (P * (1 - Λ * C) * T * D)
        (P * (N * F - Λ * C * N * F + Λ * F))))ᵀ
      (fromCols (P * (1 - Λ * C) * T * A) (fromCols (P * (1 - Λ * C) * T * D)
        (P * (N * F - Λ * C * N * F + Λ * F))))
      P).PosDef := by -- --- PROOF ---
  intro T N Λ A D C F P α β
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · -- symmetric, entry by entry
    ext ((i | i | i) | i) ((j | j | j) | j) <;> fin_cases i <;> fin_cases j <;>
      simp [fromBlocks, fromCols, T, A, D, P]
  -- some coordinate is nonzero, so the sum of squares is positive
  set x₁ := x (Sum.inl (Sum.inl 0))
  set x₂ := x (Sum.inl (Sum.inr (Sum.inl 0)))
  set x₃ := x (Sum.inl (Sum.inr (Sum.inr 0)))
  set x₄ := x (Sum.inr 0)
  have hx' : x₁ ≠ 0 ∨ x₂ ≠ 0 ∨ x₃ ≠ 0 ∨ x₄ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (funext fun k => by
      rcases k with (k | k | k) | k <;> fin_cases k <;> simp [x₁, x₂, x₃, x₄, hc.1, hc.2.1,
        hc.2.2.1, hc.2.2.2])
  have hpos : 0 < x₁ ^ 2 / 10 + x₂ ^ 2 / 4 + (x₃ / 2 + 2 * x₄ / 5) ^ 2 + x₄ ^ 2 / 25 := by
    rcases hx' with h | h | h | h
    · have := sq_pos_of_ne_zero h; positivity
    · have := sq_pos_of_ne_zero h; positivity
    · by_cases h4 : x₄ = 0
      · have h3 := sq_pos_of_ne_zero h
        have : (x₃ / 2 + 2 * x₄ / 5) ^ 2 = x₃ ^ 2 / 4 := by rw [h4]; ring
        rw [this]; positivity
      · have := sq_pos_of_ne_zero h4; positivity
    · have := sq_pos_of_ne_zero h; positivity
  -- the form, written out in the four coordinates
  simp only [star_trivial, dotProduct, mulVec, Fintype.sum_sum_type, Fin.sum_univ_one,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
    fromBlocks_apply₂₂, transpose_apply, fromCols_apply_inl, fromCols_apply_inr]
  simp [Matrix.mul_apply, T, N, Λ, A, D, C, F, P, α, β]
  nlinarith [hpos]

-- the zonotope is `⟨0, [-1  2]⟩` up to a zero generator: `3` is in it, and nothing beyond
theorem Zonotope.aux_pRadiusCounterexample_points :
    let Z := (⟨0, 0, Fin.elim0⟩ : Zonotope (Vec ℝ 1)).intersectDescriptor (0 : Mat ℝ 1 1)
      (1 : Mat ℝ 1 1) (fun _ _ => 2 : Mat ℝ 1 1) (0 : Mat ℝ 1 1) (0 : Mat ℝ 1 1)
      ((0 : Mat ℝ 1 1) * 1) (1 : Mat ℝ 1 1) ((1 : Mat ℝ 1 1) * 1) 0 0
    Z.c = 0 ∧ (fun _ => 3 : Vec ℝ 1) ∈ Z.construct ∧
      ∀ z ∈ Z.construct, |z 0| ≤ 3 := by -- --- PROOF ---
  intro Z
  -- a point of `Z` at the coefficients `b`
  have hsum : ∀ b : Fin (0 + 1 + 1 + 1) → ℝ, ∑ j : Fin (0 + 1 + 1 + 1), b j • Z.G j =
      fun _ => -b 1 + 2 * b 2 := fun b => by
    rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Z, Zonotope.intersectDescriptor, Fin.append_left, Fin.append_right,
      Fin.sum_univ_zero, Fin.sum_univ_one, zero_add]
    funext i
    fin_cases i
    simp
    ring
  -- the centre is `0`, and `3` is the point at `b = (0, -1, 1)`
  have hc : Z.c = 0 := by simp [Z, Zonotope.intersectDescriptor]
  refine ⟨hc, ⟨fun j => if j.val = 1 then -1 else if j.val = 2 then 1 else 0, fun j => ?_, ?_⟩, ?_⟩
  · dsimp only
    split_ifs <;> norm_num
  · show _ = Z.c + ∑ j : Fin (0 + 1 + 1 + 1), _
    rw [hsum, hc]
    funext i
    simp
    norm_num
  · -- every coefficient is at most `1`, so `|-b₁ + 2b₂| ≤ 3`
    rintro z ⟨b, hb, rfl⟩
    change |(Z.c + ∑ j : Fin (0 + 1 + 1 + 1), b j • Z.G j) 0| ≤ 3
    rw [hsum, hc]
    simp only [Pi.add_apply, Pi.zero_apply, zero_add]
    have h1 := hb (1 : Fin (0 + 1 + 1 + 1))
    have h2 := hb (2 : Fin (0 + 1 + 1 + 1))
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.intersectDescriptorHd_pRadius_counterexample :
    let E : Mat ℝ 1 1 := 0
    let T : Mat ℝ 1 1 := 0
    let N : Mat ℝ 1 1 := 1
    let Λ : Mat ℝ 1 1 := fun _ _ => 2
    let A : Mat ℝ 1 1 := 0
    let B : Mat ℝ 1 1 := 0
    let D : Mat ℝ 1 1 := 0
    let C : Mat ℝ 1 1 := 1
    let F : Mat ℝ 1 1 := 1
    let Hd : Mat ℝ 1 1 := 1
    let P : Mat ℝ 1 1 := fun _ _ => 1 / 5
    let α : ℝ := 1 / 2
    let β : ℝ := 1 / 2
    let γ : ℝ := 3
    -- the previous estimate `{0}`, its intersection zonotope, and Eq. 22's `ℓ_d`
    let X : Zonotope (Vec ℝ 1) := ⟨0, 0, Fin.elim0⟩
    let Z := X.intersectDescriptor T N Λ A B (D * Hd) C (F * Hd) 0 0
    let ℓd := β * sSup ((fun b : Vec ℝ 1 => (Hd *ᵥ b) ⬝ᵥ (Hd *ᵥ b)) '' {b | ∀ i, |b i| ≤ 1}) +
      (1 - β) * sSup ((fun b : Vec ℝ 1 => (Hd *ᵥ b) ⬝ᵥ (Hd *ᵥ b)) '' {b | ∀ i, |b i| ≤ 1})
    T * E + N * C = 1 ∧ P.PosDef ∧
      (fromBlocks (fromBlocks (α • P) 0 0
        (fromBlocks (((1 - α) * β) • 1) 0 0 (((1 - α) * (1 - β)) • 1)))
        (fromCols (P * (1 - Λ * C) * T * A) (fromCols (P * (1 - Λ * C) * T * D)
          (P * (N * F - Λ * C * N * F + Λ * F))))ᵀ
        (fromCols (P * (1 - Λ * C) * T * A) (fromCols (P * (1 - Λ * C) * T * D)
          (P * (N * F - Λ * C * N * F + Λ * F))))
        P).PosDef ∧
      (∀ x : Vec ℝ 1, x ⬝ᵥ x ≤ γ ^ 2 * (x ⬝ᵥ (P *ᵥ x))) ∧
      ¬ Z.pRadius P ≤ α * X.pRadius P + (1 - α) * ℓd := by -- --- PROOF ---
  intro E T N Λ A B D C F Hd P α β γ X Z ℓd
  obtain ⟨hc, h3, hbd⟩ := Zonotope.aux_pRadiusCounterexample_points
  refine ⟨by simp [T, E, N, C], ?_, Zonotope.aux_pRadiusCounterexample_lmi, fun x => ?_, ?_⟩
  · -- `P = 1/5`
    refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
    · ext i j; fin_cases i; fin_cases j; simp [P]
    · have hx0 : x 0 ≠ 0 := fun h0 => hx (funext fun i => by fin_cases i; exact h0)
      simp [P, dotProduct, mulVec]
      nlinarith [sq_pos_of_ne_zero hx0]
  · -- `x² ≤ 9 x²/5`
    simp [P, γ, dotProduct, mulVec]
    nlinarith [sq_nonneg (x 0)]
  -- the box term is `1`, `X̂_{k-1}` has P-radius `0`, and `Z` has P-radius `9/5`
  have hbox : sSup ((fun b : Vec ℝ 1 => (Hd *ᵥ b) ⬝ᵥ (Hd *ᵥ b)) '' {b | ∀ i, |b i| ≤ 1}) = 1 := by
    refine IsGreatest.csSup_eq ⟨⟨fun _ => 1, fun _ => by simp, by simp [Hd, dotProduct]⟩, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    have h := abs_le.mp (hb 0)
    simp [Hd, dotProduct]
    nlinarith [h.1, h.2]
  -- `X̂_{k-1} = {0}`
  have hX : X.pRadius P = 0 := by
    have hset : (fun z => (z - X.c) ⬝ᵥ (P *ᵥ (z - X.c))) '' X.construct = {0} := by
      ext r
      simp only [Set.mem_image, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, ⟨b, -, rfl⟩, rfl⟩; simp [X]
      · rintro rfl; exact ⟨0, ⟨Fin.elim0, fun j => j.elim0, by simp [X]⟩, by simp [X]⟩
    simp only [Zonotope.pRadius, hset, csSup_singleton]
  -- `3 ∈ Z` attains `9/5`, and `|z| ≤ 3` bounds the rest
  have hZ : 9 / 5 ≤ Z.pRadius P := by
    refine le_csSup ⟨9 / 5, ?_⟩ ⟨_, h3, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      have h := abs_le.mp (hbd z hz)
      rw [hc]
      simp [P, dotProduct, mulVec]
      nlinarith [h.1, h.2]
    · rw [hc]; simp [P, dotProduct, mulVec]; norm_num
  simp only [ℓd, hbox, hX]
  intro h
  norm_num [α, β] at h
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
