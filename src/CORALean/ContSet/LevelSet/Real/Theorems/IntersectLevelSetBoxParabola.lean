module

public import CORALean.ContSet.LevelSet.Real.Theorems.IntersectLevelSetBoxExact
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# The box `[-1, 1] × [0, 2]` cut by the parabola `x₂ = 2x₁²`

[1, Example 1]: the cut equals the Taylor model `⟨[x₁, 2x₁²]ᵀ, ∅, I⟩` and the polynomial
zonotope `{[1, 0]ᵀ α₁ + [0, 2]ᵀ α₁² | α₁ ∈ [-1, 1]}`. The first is
`intersectLevelSetBox_exact`: `2x₁²` stays in `[0, 2]` on the box and does not involve `x₂`.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem intersectLevelSetBox_parabola : -- --- CONCL ---
    let I : Interval (Vec ℝ 2) := ⟨![-1, 0], ![1, 2]⟩
    let p : Vec ℝ 2 → ℝ := fun x => 2 * x 0 ^ 2
    I.construct ∩ {x | x 1 = p x} = (intersectLevelSetBox I 1 p).construct ∧
      I.construct ∩ {x | x 1 = p x}
        = {y | ∃ α ∈ Set.Icc (-1 : ℝ) 1, y = α • ![1, 0] + α ^ 2 • ![0, 2]} := by -- --- PROOF ---
  intro I p
  refine ⟨intersectLevelSetBox_exact I 1 p (fun x hx => ?_) (fun x t => ?_), ?_⟩
  · -- `2x₁² ∈ [0, 2]` for `x₁ ∈ [-1, 1]`
    have h0 : -1 ≤ x 0 ∧ x 0 ≤ 1 := hx 0
    have hsq : x 0 ^ 2 ≤ 1 := by nlinarith [h0.1, h0.2]
    show (0 : ℝ) ≤ 2 * x 0 ^ 2 ∧ 2 * x 0 ^ 2 ≤ 2
    constructor <;> nlinarith [sq_nonneg (x 0)]
  · simp [p]
  · -- the cut is the graph of `2x₁²` over `x₁ ∈ [-1, 1]`
    ext y
    constructor
    · rintro ⟨hyI, hy⟩
      have h0 : -1 ≤ y 0 ∧ y 0 ≤ 1 := hyI 0
      refine ⟨y 0, h0, funext fun i => ?_⟩
      fin_cases i
      · simp
      · have hy1 : y 1 = 2 * y 0 ^ 2 := hy
        simp [hy1, mul_comm]
    · -- a point of the curve is in the box and on the parabola
      rintro ⟨α, hα, rfl⟩
      refine ⟨fun i => ?_, ?_⟩
      · show (![-1, 0] : Vec ℝ 2) i ≤ (α • ![1, 0] + α ^ 2 • ![0, 2] : Vec ℝ 2) i ∧
          (α • ![1, 0] + α ^ 2 • ![0, 2] : Vec ℝ 2) i ≤ (![1, 2] : Vec ℝ 2) i
        fin_cases i
        · simp [hα.1, hα.2]
        · simp
          exact ⟨sq_nonneg α, abs_le.mpr ⟨hα.1, hα.2⟩⟩
      · show (α • ![1, 0] + α ^ 2 • ![0, 2] : Vec ℝ 2) 1
          = 2 * (α • ![1, 0] + α ^ 2 • ![0, 2] : Vec ℝ 2) 0 ^ 2
        simp [mul_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
