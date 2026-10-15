module

public import CORALean.ContSet.Taylm.Real.Operations.Taylor
public import CORALean.ContSet.Taylm.Real.Theorems.PlusScaled
public import CORALean.ContSet.Taylm.Real.Theorems.PowScaled
public import CORALean.ContSet.Taylm.Real.Theorems.SmulScaled
public import CORALean.ContSet.Taylm.Real.Theorems.SumScaled
public import CORALean.ContSet.Taylm.Real.Theorems.ReachLe
public import CORALean.ContSet.Taylm.Real.Theorems.AbsConstCoefLe
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The intrinsics keep the `(n+1)`-st order scaling

[1, Thm. 1], eq. (2.9). Every elementary function here is `taylor` at its own `g` and derivative
bound `D`: a linear combination of powers of `T - c_f`, plus `D·reachᴺ⁺¹/(N+1)!`. With the
coefficients `g⁽ᵏ⁾(c_f)/k!` at most `A` and `|D| ≤ E`, a model scaled by `C` gives one scaled by
a constant in `A`, `E`, `C` and `N` alone — not in `h`. `T - c_f` weighs at most `2C`, its powers
`(8C)ᵏ` (`pow_scaled`), and `reach ≤ 2C·h` (`reach_le`) makes the last term `O(hᴺ⁺¹)`: the
source's "additional interval, the width of which scales at least with the `(n+1)`-st power".

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `T - c` at a centre no larger than `C` weighs at most twice `T`. -/
theorem Taylm.aux_minus_const_scaled {T : Taylm n} {h C : ℝ} (c : ℝ) (hc : |c| ≤ C)
    (hT : T.Scaled h C) :
    (T.minus (Taylm.const n c T.maxOrder)).Scaled h (2 * C) := by -- --- PROOF ---
  obtain ⟨w, i, s⟩ := hT
  have hC : 0 ≤ C := le_trans (abs_nonneg _) hc
  have hp : 0 ≤ C * h ^ (T.maxOrder + 1) := by
    nlinarith [abs_nonneg T.rem.inf]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Taylm.minus, Taylm.plus, Taylm.uminus, Taylm.const, max_self, Taylm.weight_append,
      neg_zero, add_zero] at *
  · have hw : Taylm.weight (List.map (fun a : ℝ × (Fin n → ℕ) => (-a.1, a.2))
        [(c, (0 : Fin n → ℕ))]) h = |c| := by
      simp [Taylm.weight, Taylm.degree]
    linarith
  · linarith
  · linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.taylor_scaled {T : Taylm n} {g : ℝ → ℝ} {D h C A E : ℝ} (h0 : 0 < h)
    (h1 : h ≤ 1) (hT : T.Scaled h C)
    (hA : ∀ k ≤ T.maxOrder, |iteratedDeriv k g T.constCoef / (Nat.factorial k : ℝ)| ≤ A)
    (hD : |D| ≤ E) :
    (T.taylor g T.constCoef D).Scaled h
      (A * ∑ k : Fin (T.maxOrder + 1), (8 * C) ^ (k : ℕ)
        + E * (2 * C) ^ (T.maxOrder + 1)) := by -- --- PROOF ---
  set N := T.maxOrder
  set c := T.constCoef
  have hC : 0 ≤ C := le_trans (Taylm.weight_nonneg _ h0) hT.1
  have hE : 0 ≤ E := le_trans (abs_nonneg _) hD
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 0 (Nat.zero_le _))
  -- `T - c` and its powers, each times its coefficient
  have hm := Taylm.aux_minus_const_scaled c (le_trans (Taylm.abs_constCoef_le T h0) hT.1) hT
  have hmo : (T.minus (Taylm.const n c N)).maxOrder = N := by
    simp [Taylm.minus, Taylm.plus, Taylm.uminus, Taylm.const, N]
  have hk : ∀ k : Fin (N + 1),
      (((T.minus (Taylm.const n c N)).pow k).smul
        (iteratedDeriv k g c / (Nat.factorial (k : ℕ) : ℝ))).Scaled h (A * (8 * C) ^ (k : ℕ)) := by
    intro k
    have hs := Taylm.smul_scaled (iteratedDeriv k g c / (Nat.factorial (k : ℕ) : ℝ))
      (Taylm.pow_scaled h0 h1 hm k)
    obtain ⟨w, i, s⟩ := hs
    have hak := hA k (Nat.lt_succ_iff.1 k.isLt)
    have h8 : (4 * (2 * C)) ^ (k : ℕ) = (8 * C) ^ (k : ℕ) := by ring_nf
    rw [h8] at w i s
    have hq : 0 ≤ (8 * C) ^ (k : ℕ) := pow_nonneg (by linarith) _
    refine ⟨le_trans w (mul_le_mul_of_nonneg_right hak hq), le_trans i ?_, le_trans s ?_⟩ <;>
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hak hq) (pow_pos h0 _).le
  -- each summand at order `N`
  have hkN : ∀ k : Fin (N + 1),
      (((T.minus (Taylm.const n c N)).pow k).smul
        (iteratedDeriv k g c / (Nat.factorial (k : ℕ) : ℝ))).maxOrder = N := by
    intro k
    simp only [Taylm.smul, Taylm.pow_maxOrder, hmo]
  obtain ⟨w, i, s, o⟩ := Taylm.sum_scaled hkN hk
  -- the Lagrange remainder carries `reachᴺ⁺¹ ≤ (2Ch)ᴺ⁺¹`
  have hr := Taylm.reach_le h0 h1 hT
  have hr0 : 0 ≤ T.reach c := le_trans (abs_nonneg _) (le_max_left _ _)
  have hρ : |D * T.reach c ^ (N + 1) / ((N + 1).factorial : ℝ)|
      ≤ E * (2 * C) ^ (N + 1) * h ^ (N + 1) := by
    have hf : (1 : ℝ) ≤ ((N + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [abs_div, abs_mul, abs_pow, abs_of_nonneg hr0, Nat.abs_cast, div_le_iff₀ (by linarith)]
    have : T.reach c ^ (N + 1) ≤ (2 * C * h) ^ (N + 1) := pow_le_pow_left₀ hr0 hr _
    have h2 : 0 ≤ (2 * C * h) ^ (N + 1) := pow_nonneg (by positivity) _
    calc |D| * T.reach c ^ (N + 1) ≤ E * (2 * C * h) ^ (N + 1) :=
          mul_le_mul hD this (pow_nonneg hr0 _) hE
      _ ≤ E * (2 * C * h) ^ (N + 1) * ((N + 1).factorial : ℝ) :=
          le_mul_of_one_le_right (mul_nonneg hE h2) hf
      _ = E * (2 * C) ^ (N + 1) * h ^ (N + 1) * ((N + 1).factorial : ℝ) := by ring
  -- the result's order is at most `N`, so `hᴺ⁺¹` is the smaller power
  have hmo' : (T.taylor g c D).maxOrder ≤ N := by
    simp only [Taylm.taylor, Taylm.compose, Taylm.plus]
    exact max_le o (Nat.zero_le _)
  have hpow : h ^ (N + 1) ≤ h ^ ((T.taylor g c D).maxOrder + 1) :=
    pow_le_pow_of_le_one h0.le h1 (by omega)
  have hS : 0 ≤ A * ∑ k : Fin (N + 1), (8 * C) ^ (k : ℕ) :=
    mul_nonneg hA0 (Finset.sum_nonneg fun k _ => pow_nonneg (by linarith) _)
  have hS' : 0 ≤ E * (2 * C) ^ (N + 1) := mul_nonneg hE (pow_nonneg (by linarith) _)
  rw [← Finset.mul_sum] at w i s
  have hK : 0 ≤ A * ∑ k : Fin (N + 1), (8 * C) ^ (k : ℕ) + E * (2 * C) ^ (N + 1) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [Taylm.taylor, Taylm.compose, Taylm.plus, Taylm.weight_append]
    simp only [Taylm.weight, List.map_nil, List.sum_nil, add_zero] at w ⊢
    linarith
  -- the two remainder ends: the sum's, then the Lagrange term's
  · refine le_trans ?_ (mul_le_mul_of_nonneg_left hpow hK)
    simp only [Taylm.taylor, Taylm.compose, Taylm.plus]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_neg]
    nlinarith [hρ, i, (pow_pos h0 (N + 1)).le]
  · refine le_trans ?_ (mul_le_mul_of_nonneg_left hpow hK)
    simp only [Taylm.taylor, Taylm.compose, Taylm.plus]
    refine le_trans (abs_add_le _ _) ?_
    nlinarith [hρ, s, (pow_pos h0 (N + 1)).le]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
