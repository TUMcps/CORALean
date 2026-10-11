import CORALean.ContDynamics.LinearSysDT.Definitions.FaultRadiusLmi
import CORALean.ContSet.Zonotope.Real.Definitions.PRadius
import CORALean.ContSet.Zonotope.Real.Operations.FaultObserve
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBy
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# The printed P-radius contraction fails after a reduction

[1, Eq. 16] (equivalently [1, Eq. 17] at `W = PL`) is derived as sufficient for
`ℓ_{k+1} ≤ γ ℓ_k + ε` [1, Eq. 14], `ℓ_k = max_b ‖H_k b‖²_P` [1, Eq. 13]. The next zonotope
[1, Eq. 10] is built from `↓_q(H_k)`, whose P-radius can exceed `H_k`'s, and the derivation's
`θ = H_k b` ranges over `H_k` only. In `ℝ²` with `A = (9/10) I`, `B = 0`, `C = 0`, `L = 0` (so
`W = 0`), no disturbance or noise (`ε = 0`), `P = I`, `γ = 9/10` and
`H_k = [(2, 0) (1, 1) (1, -1)]`: Eq. 17 holds (`a² = 81/100 < γ`), `ℓ_k = 16` (at most, attained at
`b = (1, 1, 1)`), `↓_1(H_k) = [(2, 0) (2, 0) (0, 2)]` keeps the longest column and boxes the other
two (`Zonotope.reduceBy` at `Partition.split 1 2`), and
`ℓ_{k+1} = (81/100) · 20 = 81/5 > 72/5 = γ ℓ_k`.
With `ℓ_k` read as the P-radius of `↓_q(H_k)` the bound holds (`Zonotope.faultObserve_pRadius_le`).

## References

* [1] Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer
      with H− Performance". In Proc. of the 36th Chinese Control Conference (CCC),
      pp. 7230-7235, 2017.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- simp evaluates the form of Eq. 17's concrete `4 × 4` block matrix entry by entry
set_option maxHeartbeats 100000 in
theorem Zonotope.aux_faultRadiusCounterexample_lmi :
    LinearSysDT.FaultRadiusLmi (n := 2) (ny := 1) (nw := 0) (nv := 0) (rw := 0) (rv := 0)
      ((9 / 10 : ℝ) • 1) 0 0 0 0 0 1 0 (9 / 10) := by -- --- PROOF ---
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · -- symmetric, entry by entry
    ext ((i | i | i) | i) ((j | j | j) | j) <;> fin_cases i <;> fin_cases j <;>
      simp [fromBlocks, fromRows]
  -- per coordinate `(9/10)θ² - (9/5)θw + w² = (w - 9θ/10)² + 9θ²/100`, positive off `0`
  set θ₀ := x (Sum.inl (Sum.inl 0))
  set θ₁ := x (Sum.inl (Sum.inl 1))
  set w₀ := x (Sum.inr 0)
  set w₁ := x (Sum.inr 1)
  have hx' : θ₀ ≠ 0 ∨ θ₁ ≠ 0 ∨ w₀ ≠ 0 ∨ w₁ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (funext fun k => by
      rcases k with (k | k | k) | k <;> fin_cases k <;> simp [θ₀, θ₁, w₀, w₁, hc.1, hc.2.1,
        hc.2.2.1, hc.2.2.2])
  have hpos : 0 < (w₀ - 9 / 10 * θ₀) ^ 2 + 9 / 100 * θ₀ ^ 2 + (w₁ - 9 / 10 * θ₁) ^ 2 +
      9 / 100 * θ₁ ^ 2 := by
    -- whichever coordinate is nonzero makes one square positive
    have a := sq_nonneg (w₀ - 9 / 10 * θ₀)
    have b := sq_nonneg (w₁ - 9 / 10 * θ₁)
    have c := sq_nonneg θ₀
    have d := sq_nonneg θ₁
    rcases hx' with h | h | h | h
    · have := sq_pos_of_ne_zero h; linarith
    · have := sq_pos_of_ne_zero h; linarith
    · by_cases h0 : θ₀ = 0
      · have : (w₀ - 9 / 10 * θ₀) ^ 2 = w₀ ^ 2 := by rw [h0]; ring
        have := sq_pos_of_ne_zero h; linarith
      · have := sq_pos_of_ne_zero h0; linarith
    · by_cases h1 : θ₁ = 0
      · have : (w₁ - 9 / 10 * θ₁) ^ 2 = w₁ ^ 2 := by rw [h1]; ring
        have := sq_pos_of_ne_zero h; linarith
      · have := sq_pos_of_ne_zero h1; linarith
  -- the form, written out in the four coordinates
  simp only [star_trivial, dotProduct, mulVec, Fintype.sum_sum_type, Fin.sum_univ_two,
    Fin.sum_univ_zero]
  simp
  nlinarith [hpos]

-- the instance's state zonotope `⟨0, [(2, 0) (1, 1) (1, -1)]⟩` at the coefficients `b`
theorem Zonotope.aux_faultRadiusCounterexample_sumK (b : Fin 3 → ℝ) :
    let Xk : Zonotope (Vec ℝ 2) := ⟨3, 0, ![![2, 0], ![1, 1], ![1, -1]]⟩
    ∑ j, b j • Xk.G j = ![2 * b 0 + b 1 + b 2, b 1 - b 2] := by
  intro Xk
  funext i
  fin_cases i <;> simp [Xk, Fin.sum_univ_three] <;> ring

-- the next zonotope: `↓_1` keeps `(2, 0)` and boxes the rest into `diag(2, 2)`, then `A = 9/10`
theorem Zonotope.aux_faultRadiusCounterexample_sumP (b : Fin (1 + 2 + 0 + 0) → ℝ) :
    let A : Mat ℝ 2 2 := (9 / 10 : ℝ) • 1
    let Xk : Zonotope (Vec ℝ 2) := ⟨3, 0, ![![2, 0], ![1, 1], ![1, -1]]⟩
    let Xp := (Xk.reduceBy (Partition.split 1 2)).faultObserve A (0 : Mat ℝ 2 1)
      (0 : Mat ℝ 1 2) (0 : Mat ℝ 2 1) (0 : Mat ℝ 2 0) (0 : Mat ℝ 0 0) (0 : Mat ℝ 1 0)
      (0 : Mat ℝ 0 0) 0 0
    Xp.c = 0 ∧ ∑ j : Fin Xp.h, b j • Xp.G j =
      ![9 / 10 * (2 * b 0 + 2 * b 1), 9 / 10 * (2 * b 2)] := by -- --- PROOF ---
  intro A Xk Xp
  refine ⟨by simp [Xp, A, Zonotope.faultObserve, Zonotope.reduceBy, Xk], ?_⟩
  show ∑ j : Fin (1 + 2 + 0 + 0), b j • Xp.G j = _
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Xp, Zonotope.faultObserve, Zonotope.reduceBy, Fin.append_left, Fin.append_right,
    Fin.sum_univ_zero, add_zero]
  have h1 : (Partition.split 1 2).left 0 = 0 := rfl
  have h2 : (Partition.split 1 2).right 0 = 1 := rfl
  have h3 : (Partition.split 1 2).right 1 = 2 := rfl
  simp only [Fin.sum_univ_one, Fin.sum_univ_two, h1, h2, h3]
  funext i
  fin_cases i <;> simp [Xk, A, Matrix.mulVec, dotProduct, Fin.sum_univ_two, diagonal] <;>
    norm_num <;> ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.faultObserve_pRadius_counterexample :
    let A : Mat ℝ 2 2 := (9 / 10 : ℝ) • 1
    let B : Mat ℝ 2 1 := 0
    let C : Mat ℝ 1 2 := 0
    let L : Mat ℝ 2 1 := 0
    let Dx : Mat ℝ 2 0 := 0                                   -- no disturbance
    let Hw : Mat ℝ 0 0 := 0
    let Dy : Mat ℝ 1 0 := 0                                   -- no noise
    let Hv : Mat ℝ 0 0 := 0
    let P : Mat ℝ 2 2 := 1
    let γ : ℝ := 9 / 10
    let ε : ℝ := 0                                            -- Eq. 15 over empty boxes
    let Xk : Zonotope (Vec ℝ 2) := ⟨3, 0, ![![2, 0], ![1, 1], ![1, -1]]⟩
    let Xp := (Xk.reduceBy (Partition.split 1 2)).faultObserve A B C L Dx Hw Dy Hv 0 0
    LinearSysDT.FaultRadiusLmi A C Dx Hw Dy Hv P (P * L) γ ∧ 0 < γ ∧ γ < 1 ∧
      ¬ Xp.pRadius P ≤ γ * Xk.pRadius P + ε := by -- --- PROOF ---
  intro A B C L Dx Hw Dy Hv P γ ε Xk Xp
  have hW : P * L = 0 := by simp [P, L]
  refine ⟨hW ▸ Zonotope.aux_faultRadiusCounterexample_lmi, by norm_num [γ], by norm_num [γ], ?_⟩
  -- `ℓ_k ≤ 16`
  have hK : Xk.pRadius P ≤ 16 := by
    refine csSup_le ⟨_, Xk.c, ⟨0, by simp, by simp⟩, rfl⟩ ?_
    rintro _ ⟨z, ⟨b, hb, rfl⟩, rfl⟩
    have hs := Zonotope.aux_faultRadiusCounterexample_sumK b
    have h0 := abs_le.mp (hb 0)
    have h1 := abs_le.mp (hb 1)
    have h2 := abs_le.mp (hb 2)
    simp only [add_sub_cancel_left]
    rw [hs]
    simp [P, dotProduct, Fin.sum_univ_two]
    nlinarith [mul_nonneg (sub_nonneg.mpr h0.2) (sub_nonneg.mpr h1.2),
      mul_nonneg (sub_nonneg.mpr h0.2) (sub_nonneg.mpr h2.2),
      mul_nonneg (sub_nonneg.mpr h1.2) (sub_nonneg.mpr h2.2),
      mul_nonneg (neg_le_iff_add_nonneg.mp h0.1) (neg_le_iff_add_nonneg.mp h1.1),
      mul_nonneg (neg_le_iff_add_nonneg.mp h0.1) (neg_le_iff_add_nonneg.mp h2.1),
      mul_nonneg (neg_le_iff_add_nonneg.mp h1.1) (neg_le_iff_add_nonneg.mp h2.1),
      mul_nonneg (sub_nonneg.mpr h0.2) (neg_le_iff_add_nonneg.mp h0.1),
      mul_nonneg (sub_nonneg.mpr h1.2) (neg_le_iff_add_nonneg.mp h1.1),
      mul_nonneg (sub_nonneg.mpr h2.2) (neg_le_iff_add_nonneg.mp h2.1)]
  -- `ℓ_{k+1} ≥ 81/5`, attained at all coefficients `1`, and nothing larger
  have hP : 81 / 5 ≤ Xp.pRadius P := by
    refine le_csSup ⟨81 / 5, ?_⟩ ⟨Xp.c + ∑ j, (fun _ => (1 : ℝ)) j • Xp.G j,
      ⟨fun _ => 1, fun _ => by simp, rfl⟩, ?_⟩
    · -- every point is `(9/10)(2b₀ + 2b₁, 2b₂)`, at most `81/5` away
      rintro _ ⟨z, ⟨b, hb, rfl⟩, rfl⟩
      obtain ⟨-, hs⟩ := Zonotope.aux_faultRadiusCounterexample_sumP b
      have h0 := abs_le.mp (hb (0 : Fin (1 + 2 + 0 + 0)))
      have h1 := abs_le.mp (hb (1 : Fin (1 + 2 + 0 + 0)))
      have h2 := abs_le.mp (hb (2 : Fin (1 + 2 + 0 + 0)))
      simp only [add_sub_cancel_left]
      rw [hs]
      -- `(2b₀ + 2b₁)² ≤ 16` and `(2b₂)² ≤ 4` from the box
      simp [P, dotProduct, Fin.sum_univ_two]
      nlinarith [mul_nonneg (sub_nonneg.mpr h0.2) (sub_nonneg.mpr h1.2),
        mul_nonneg (neg_le_iff_add_nonneg.mp h0.1) (neg_le_iff_add_nonneg.mp h1.1),
        mul_nonneg (sub_nonneg.mpr h0.2) (neg_le_iff_add_nonneg.mp h0.1),
        mul_nonneg (sub_nonneg.mpr h1.2) (neg_le_iff_add_nonneg.mp h1.1),
        mul_nonneg (sub_nonneg.mpr h2.2) (neg_le_iff_add_nonneg.mp h2.1)]
    · obtain ⟨-, hs⟩ := Zonotope.aux_faultRadiusCounterexample_sumP (fun _ => 1)
      simp only [add_sub_cancel_left]
      rw [hs]
      simp [P, dotProduct, Fin.sum_univ_two]
      norm_num
  intro h
  norm_num [γ, ε] at h
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
