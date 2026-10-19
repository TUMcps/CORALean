module

public import CORALean.NN.Layers.Theorems.Real.ApproxErrorIsExtreme
public import CORALean.NN.Layers.Theorems.Real.EqPmArtanhOfTanh
public import CORALean.NN.Layers.Theorems.Real.ExistsCriticalExtreme
public import CORALean.Global.ElementaryDerivBounds
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

/-!
# The approximation errors of the hyperbolic tangent

[1, Prop. 10]: for `ϕ = tanh`, `e_low = min_{x ∈ P ∩ [l,u]} ϕ(x) - p(x)` and `e_up = max_{x ∈ P ∩
[l,u]} ϕ(x) - p(x)` with `P_tanh = {±tanh⁻¹(√(1 - m)), l, u}`, `p(x) = m x`. As in the paper's
proof: the extremes of `tanh(x) - m x` over `[l, u]` are at the bounds or where the derivative
`1 - tanh(x)²` equals `m`, that is `tanh(x) = ±√(1 - m)`. It holds for every slope `m` and every
`l ≤ u`: that `p` is the secant of [1, Def. 7] is not used. Where `m > 1` there is no such point,
`√(1 - m)` is zero in Lean and the point `0` it adds is harmless.

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

theorem approxError_tanh (m l u : ℝ) (hlu : l ≤ u) : -- --- CONCL ---
    IsLeast ((fun x => Real.tanh x - (fun x => m * x) x) ''
          (({Real.artanh (√(1 - m)), -Real.artanh (√(1 - m)), l, u} : Set ℝ) ∩ Set.Icc l u))
        (approxErrorLow Real.tanh (fun x => m * x) l u) ∧
      IsGreatest ((fun x => Real.tanh x - (fun x => m * x) x) ''
          (({Real.artanh (√(1 - m)), -Real.artanh (√(1 - m)), l, u} : Set ℝ) ∩ Set.Icc l u))
        (approxErrorUp Real.tanh (fun x => m * x) l u) := by -- --- PROOF ---
  obtain ⟨⟨a, haI, ha, hac⟩, ⟨b, hbI, hb, hbc⟩⟩ := exists_critical_extreme Real.tanh
    (fun x => 1 - Real.tanh x ^ 2) m l u _root_.CORALean.hasDerivAt_tanh hlu
  -- a critical point is one of the two `±artanh √(1 - m)`
  have hcrit : ∀ q, 1 - Real.tanh q ^ 2 = m →
      q = Real.artanh (√(1 - m)) ∨ q = -Real.artanh (√(1 - m)) := fun q hq => by
    have h1 : 0 ≤ 1 - m := by nlinarith [sq_nonneg (Real.tanh q)]
    have h2 : Real.tanh q ^ 2 = √(1 - m) ^ 2 := by rw [Real.sq_sqrt h1]; linarith
    refine eq_pm_artanh_of_tanh q (√(1 - m)) (Real.sqrt_nonneg _) ?_ h2
    rw [Real.sqrt_lt' one_pos]; nlinarith [Real.tanh_sq_lt_one q]
  have hmem : ∀ q ∈ Set.Icc l u, (q = l ∨ q = u ∨ 1 - Real.tanh q ^ 2 = m) →
      q ∈ (({Real.artanh (√(1 - m)), -Real.artanh (√(1 - m)), l, u} : Set ℝ) ∩ Set.Icc l u) :=
    fun q hq h => by
      refine ⟨?_, hq⟩
      rcases h with h | h | h
      · simp [h]
      · simp [h]
      · rcases hcrit q h with h | h <;> simp [h]
  exact approxError_isExtreme Real.tanh (fun x => m * x) _ l u
    (Set.toFinite _) ⟨a, hmem a haI hac⟩
    (fun x hx => ⟨a, hmem a haI hac, ha x hx⟩)
    (fun x hx => ⟨b, hmem b hbI hbc, hb x hx⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
