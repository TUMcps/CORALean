module

public import CORALean.ContDynamics.LinearARX.Operations.Alg2
public import CORALean.ContDynamics.LinearARX.Definitions.ReachWindowExact
public import CORALean.ContDynamics.LinearARX.Theorems.StackSimulateZero
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Alg. 2 started past `p` misses reachable windows

[1, Thm. 3] claims [1, Alg. 2] for every `k_init ≥ p`. Line 18 builds `T_c2` from the stored
`B̃ᵢ` at `i = k_init … k_init + p - 1`, needing `B̃ᵢ(k_init + p)`; lines 14–15 refresh only
`i < 2p`, so for `k_init > p` it reads `B̃ᵢ(k_init)` at `i ≥ 2p`, which differs. Here
`y(k) = y(k-1) + ũ(k)`, `p = 1`, `ũ ∈ [-1, 1]`, `y(0) = 0`, `k_init = 2`: the second pass
should return `y(3) ∈ [-3, 3]` and returns `[-2, 2]`, dropping `B̃₂(3) Ũ_c = Ũ_c`. Unsound
for an outer approximation; CORA's `reach` always starts at `k_init = p` and is not hit.

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the
  62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.alg2_ne_reachWindowExact : -- --- STMT ---
    let sys : LinearARX ℝ 1 1 1 := ⟨fun _ => 1, fun j => if j.val = 0 then 1 else 0, 1⟩
    let Uc : Set (Vec ℝ 1) := {v | |v 0| ≤ 1}
    (fun _ => 3) ∈ sys.reachWindowExact 0 (fun _ => Uc + {0}) (2 + 1 * 1) ∧
      (fun _ => 3) ∉ sys.alg2 0 Uc (fun _ => 0) 2 1 := by -- --- PROOF ---
  intro sys Uc
  constructor
  · -- all inputs `1`: `y(k) = k`
    let u : ℕ → Vec ℝ 1 := fun _ _ => 1
    have hsim : ∀ k : ℕ, sys.simulate 0 u k 0 = k := by
      intro k
      induction k with
      | zero =>
        rw [LinearARX.simulate, dif_pos (by norm_num)]
        simp
      | succ k ih =>
        -- `y(k+1) = y(k) + ũ(k+1)`
        rw [LinearARX.simulate, dif_neg (by omega)]
        have hA0 : sys.Abar 0 = 1 := rfl
        have hB0 : sys.Bbar 0 = 1 := by simp [sys]
        have hB1 : sys.Bbar 1 = 0 := by simp [sys]
        simp only [Fin.sum_univ_one, Pi.add_apply, Scalar.toRealMat_real, hA0, one_mulVec,
          Fin.val_zero, zero_add, Nat.add_sub_cancel]
        rw [ih, Fin.sum_univ_succ, Fin.sum_univ_one, Fin.succ_zero_eq_one, hB0, hB1, one_mulVec,
          zero_mulVec, add_zero]
        simp [u]
    -- the run, with `ũ = 1 + 0 ∈ Ũ_c + ũ_v`, reaches `y(3) = 3`
    refine ⟨sys.simulate 0 u, u, sys.stack_simulate_zero 0 u, fun i => ⟨u i, by simp [Uc, u],
      0, rfl, add_zero _⟩, fun k hk => by rw [LinearARX.simulate, dif_neg (by omega)], ?_⟩
    funext r
    rw [show r = finProdFinEquiv ((0 : Fin 1), (0 : Fin 1)) from Fin.ext (by simp)]
    show (3 : ℝ) = sys.simulate 0 u (2 + 1 * 1 + (finProdFinEquiv.symm (finProdFinEquiv
      ((0 : Fin 1), (0 : Fin 1)))).1) (finProdFinEquiv.symm (finProdFinEquiv
      ((0 : Fin 1), (0 : Fin 1)))).2
    rw [Equiv.symm_apply_apply]
    simp only [Fin.val_zero, add_zero]
    rw [hsim]
    norm_num
  · -- the second pass returns `[-2, 2]`
    have hA : sys.Aext = 1 := by
      ext r c
      rw [show r = 0 from Fin.ext (by simp), show c = 0 from Fin.ext (by simp)]
      simp [LinearARX.Aext, LinearARX.toLinearSysDT, sys, Scalar.toRealMat_real]
    -- `Ā_ext = 1`, `B̄_ext,0 = 1` and the other lags zero, so `B̃ᵢ(k)` counts `j < k` with `j = i`
    have hB : ∀ i : ℤ, sys.Bext i 0 0 = if i = 0 then 1 else 0 := by
      intro i
      simp only [LinearARX.Bext, Nat.cast_one]
      split_ifs with h h'
      · subst h'
        simp only [LinearARX.inputMat, sys, Scalar.toRealMat_real, Matrix.of_apply]
        rw [Fin.fin_one_eq_zero ((finProdFinEquiv.symm (0 : Fin (1 * 1))).2)]
        simp
      · have hi : i = 1 := by omega
        subst hi
        simp [LinearARX.inputMat, sys]
      · omega
      · rfl
    have hBt : ∀ (k : ℕ) (i : ℤ), sys.Btilde k i 0 0
        = ∑ j ∈ Finset.range k, if i - j = 0 then 1 else 0 := by
      intro k i
      unfold LinearARX.Btilde
      rw [Matrix.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hA, one_pow, Matrix.one_mul, hB]
    -- every point of `(M ·) '' Uc` is bounded by `|M₀₀|`
    have himg : ∀ (M : Mat ℝ 1 1) (x : Vec ℝ 1), x ∈ (M *ᵥ ·) '' Uc → |x 0| ≤ |M 0 0| := by
      rintro M x ⟨v, hv, rfl⟩
      have hv' : |v 0| ≤ 1 := hv
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, abs_mul]
      nlinarith [abs_nonneg (M 0 0), abs_nonneg (v 0)]
    -- the pass: `B̃₀(2) Ũ_c + B̃₁(2) Ũ_c + B̃₂(2) Ũ_c + Ā_ext B̃₂(2) Ũ_c`, the stale `B̃₂(2) = 0`
    intro hx
    simp only [LinearARX.alg2, LinearARX.aux_alg2State] at hx
    norm_num at hx
    rw [Finset.sum_range_succ, Finset.sum_range_one] at hx
    obtain ⟨a, ha, d, hd, had⟩ := hx
    obtain ⟨b, hb, c, hc, hbc⟩ := ha
    obtain ⟨e, he, g, hg, heg⟩ := hb
    rw [Set.image_image] at hd
    have v0 : sys.Btilde 2 0 0 0 = 1 := by
      rw [hBt, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    have v1 : sys.Btilde 2 1 0 0 = 1 := by
      rw [hBt, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    have v2 : sys.Btilde 2 2 0 0 = 0 := by
      rw [hBt, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    -- so every point is within `1 + 1 + 0 + 0` of the origin
    have be := himg _ e he
    have bg := himg _ g hg
    have bc := himg _ c hc
    have bd := himg (sys.Aext * sys.Btilde 2 2) d (by
      obtain ⟨v, hv, rfl⟩ := hd
      exact ⟨v, hv, (mulVec_mulVec _ _ _).symm⟩)
    rw [hA, Matrix.one_mul] at bd
    rw [Nat.cast_zero, v0] at be
    rw [Nat.cast_one, v1] at bg
    rw [v2] at bc bd
    have e3 := congrFun had 0
    have ea := congrFun hbc 0
    have eb := congrFun heg 0
    simp only [Pi.add_apply] at e3 ea eb
    norm_num at be bg bc bd
    have := abs_le.mp be
    have := abs_le.mp bg
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
