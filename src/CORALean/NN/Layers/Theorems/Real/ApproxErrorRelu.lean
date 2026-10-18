module

public import CORALean.NN.Layers.Definitions.Relu
public import CORALean.NN.Layers.Theorems.Real.ApproxErrorIsExtreme
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The approximation errors of ReLU

[1, Prop. 10]: for `ϕ = ReLU`, `e_low = min_{x ∈ P ∩ [l,u]} ϕ(x) - p(x)` and `e_up = max_{x ∈ P ∩
[l,u]} ϕ(x) - p(x)` with `P_ReLU = {0, l, u}`, `p(x) = m x`. As in the paper's proof, `ReLU(x) -
m x` is linear on `[l, 0]` and on `[0, u]`, so its extremes are at the bounds and at `0` where
`0 ∈ [l, u]`. It holds for every slope `m` and every `l ≤ u`: that `p` is the secant of [1, Def. 7]
is not used.

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The points of `{0, l, u}` in `[l, u]` dominate `ReLU(x) - m x` from below. -/
theorem aux_relu_dominated_below (m l u x : ℝ) (hxl : l ≤ x) (hxu : x ≤ u) :
    ∃ q ∈ ({0, l, u} : Set ℝ) ∩ Set.Icc l u, relu q - m * q ≤ relu x - m * x := by -- --- PROOF ---
  have hlu : l ≤ u := hxl.trans hxu
  simp only [relu]
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx]
    rcases le_total 0 (1 - m) with hm | hm
    · rcases le_total l 0 with hl | hl
      · exact ⟨0, ⟨by simp, hl, hx.trans hxu⟩, by simp; nlinarith⟩
      · refine ⟨l, ⟨by simp, le_rfl, hlu⟩, ?_⟩
        rw [max_eq_left hl]; nlinarith
    · refine ⟨u, ⟨by simp, hlu, le_rfl⟩, ?_⟩
      rw [max_eq_left (hx.trans hxu)]; nlinarith
  · rw [max_eq_right hx]
    rcases le_total 0 m with hm | hm
    · rcases le_total 0 u with hu | hu
      · exact ⟨0, ⟨by simp, hxl.trans hx, hu⟩, by simp; nlinarith⟩
      · refine ⟨u, ⟨by simp, hlu, le_rfl⟩, ?_⟩
        rw [max_eq_right hu]; nlinarith
    · refine ⟨l, ⟨by simp, le_rfl, hlu⟩, ?_⟩
      rw [max_eq_right (hxl.trans hx)]; nlinarith

/-- The points of `{0, l, u}` in `[l, u]` dominate `ReLU(x) - m x` from above. -/
theorem aux_relu_dominated_above (m l u x : ℝ) (hxl : l ≤ x) (hxu : x ≤ u) :
    ∃ q ∈ ({0, l, u} : Set ℝ) ∩ Set.Icc l u, relu x - m * x ≤ relu q - m * q := by -- --- PROOF ---
  have hlu : l ≤ u := hxl.trans hxu
  simp only [relu]
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx]
    rcases le_total 0 (1 - m) with hm | hm
    · refine ⟨u, ⟨by simp, hlu, le_rfl⟩, ?_⟩
      rw [max_eq_left (hx.trans hxu)]; nlinarith
    · rcases le_total l 0 with hl | hl
      · exact ⟨0, ⟨by simp, hl, hx.trans hxu⟩, by simp; nlinarith⟩
      · refine ⟨l, ⟨by simp, le_rfl, hlu⟩, ?_⟩
        rw [max_eq_left hl]; nlinarith
  · rw [max_eq_right hx]
    rcases le_total 0 m with hm | hm
    · refine ⟨l, ⟨by simp, le_rfl, hlu⟩, ?_⟩
      rw [max_eq_right (hxl.trans hx)]; nlinarith
    · rcases le_total 0 u with hu | hu
      · exact ⟨0, ⟨by simp, hxl.trans hx, hu⟩, by simp; nlinarith⟩
      · refine ⟨u, ⟨by simp, hlu, le_rfl⟩, ?_⟩
        rw [max_eq_right hu]; nlinarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem approxError_relu (m l u : ℝ) (hlu : l ≤ u) : -- --- STMT ---
    IsLeast ((fun x => relu x - (fun x => m * x) x) '' (({0, l, u} : Set ℝ) ∩ Set.Icc l u))
        (approxErrorLow relu (fun x => m * x) l u) ∧
      IsGreatest ((fun x => relu x - (fun x => m * x) x) '' (({0, l, u} : Set ℝ) ∩ Set.Icc l u))
        (approxErrorUp relu (fun x => m * x) l u) := by -- --- PROOF ---
  exact approxError_isExtreme relu (fun x => m * x) {0, l, u} l u
    (Set.toFinite _) ⟨l, by simp, le_rfl, hlu⟩
    (fun x hx => aux_relu_dominated_below m l u x hx.1 hx.2)
    (fun x hx => aux_relu_dominated_above m l u x hx.1 hx.2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
