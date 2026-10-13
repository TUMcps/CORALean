module

public import CORALean.NN.Layers.Theorems.Real.ApproxErrorTanh
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid
public import CORALean.NN.Layers.Theorems.Real.SigmoidNeg
public import CORALean.NN.Layers.Theorems.Real.TanhEqSigmoid

@[expose] public section

/-!
# The approximation errors of the logistic sigmoid

[1, Prop. 10]: for `ϕ = σ`, `e_low = min_{x ∈ P ∩ [l,u]} ϕ(x) - p(x)` and `e_up = max_{x ∈ P ∩
[l,u]} ϕ(x) - p(x)` with `P_σ = {±2 tanh⁻¹(√(1 - 4m)), l, u}`, `p(x) = m x`. As in the paper's
proof: the extremes of `σ(x) - m x` over `[l, u]` are at the bounds or where `σ'(x) = m`, and with
`σ(x) = (tanh(x/2) + 1)/2` that is `(1 - tanh(x/2)²)/4 = m`, `tanh(x/2) = ±√(1 - 4m)`. It holds for
every slope `m` and every `l ≤ u`: that `p` is the secant of [1, Def. 7] is not used. Where `m >
1/4` there is no such point, `√(1 - 4m)` is zero in Lean and the point `0` it adds is harmless.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem approxError_sigmoid (m l u : ℝ) (hlu : l ≤ u) :
    IsLeast ((fun x => sigmoid x - (fun x => m * x) x) ''
          (({2 * Real.artanh (√(1 - 4 * m)), -(2 * Real.artanh (√(1 - 4 * m))), l, u} : Set ℝ) ∩
            Set.Icc l u))
        (approxErrorLow sigmoid (fun x => m * x) l u) ∧
      IsGreatest ((fun x => sigmoid x - (fun x => m * x) x) ''
          (({2 * Real.artanh (√(1 - 4 * m)), -(2 * Real.artanh (√(1 - 4 * m))), l, u} : Set ℝ) ∩
            Set.Icc l u))
        (approxErrorUp sigmoid (fun x => m * x) l u) := by -- --- PROOF ---
  obtain ⟨⟨a, haI, ha, hac⟩, ⟨b, hbI, hb, hbc⟩⟩ := exists_critical_extreme sigmoid
    sigmoidDeriv m l u hasDerivAt_sigmoid hlu
  -- a critical point is one of the two `±2 artanh √(1 - 4m)`
  have hcrit : ∀ q, sigmoidDeriv q = m →
      q = 2 * Real.artanh (√(1 - 4 * m)) ∨ q = -(2 * Real.artanh (√(1 - 4 * m))) :=
    fun q hq => by
      have hT : Real.tanh (q / 2) = 2 * sigmoid q - 1 := by
        rw [tanh_eq_sigmoid, show 2 * (q / 2) = q by ring]
      -- `σ' = σ (1 - σ) = (1 - tanh(q/2)²) / 4`
      have hd : sigmoidDeriv q = (1 - Real.tanh (q / 2) ^ 2) / 4 := by
        rw [sigmoidDeriv, sigmoid_neg, hT]; ring
      have h1 : 0 ≤ 1 - 4 * m := by nlinarith [sq_nonneg (Real.tanh (q / 2))]
      have h2 : Real.tanh (q / 2) ^ 2 = √(1 - 4 * m) ^ 2 := by
        rw [Real.sq_sqrt h1]; linarith
      have h3 : √(1 - 4 * m) < 1 := by
        rw [Real.sqrt_lt' one_pos]; nlinarith [Real.tanh_sq_lt_one (q / 2)]
      -- so `tanh(q/2) = ±√(1 - 4m)`
      rcases eq_pm_artanh_of_tanh (q / 2) (√(1 - 4 * m)) (Real.sqrt_nonneg _) h3 h2 with h | h
      · left; linarith
      · right; linarith
  -- the bounds and the critical points are the candidates
  have hmem : ∀ q ∈ Set.Icc l u, (q = l ∨ q = u ∨ sigmoidDeriv q = m) →
      q ∈ (({2 * Real.artanh (√(1 - 4 * m)), -(2 * Real.artanh (√(1 - 4 * m))), l, u} :
        Set ℝ) ∩ Set.Icc l u) :=
    fun q hq h => by
      refine ⟨?_, hq⟩
      rcases h with h | h | h
      · simp [h]
      · simp [h]
      · rcases hcrit q h with h | h <;> simp [h]
  exact approxError_isExtreme sigmoid (fun x => m * x) _ l u
    (Set.toFinite _) ⟨a, hmem a haI hac⟩
    (fun x hx => ⟨a, hmem a haI hac, ha x hx⟩)
    (fun x hx => ⟨b, hmem b hbI hbc, hb x hx⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
