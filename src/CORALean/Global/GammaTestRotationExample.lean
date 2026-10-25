module

public import CORALean.Global.PassesGammaTest
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The unpreconditioned test fails on a rotation

[1, Example 4.1]: `f(x) = M x`, `M = (1 1; -1 1)`, `x = [-2, 2]²`, `y = [-ε, ε]²`, `x₀ = 0` (the
paper's `x̃`) and `J = M`. The image of `x` is `x` rotated by `π/4` and inflated by `√2`, so
`y ⊆ range(f, x)` holds if and only if `ε ≤ 2`; yet (2) of [1, Cor. 3.1], `PassesGammaTest`, fails
for every `ε > 0`, because `M` is not an H-matrix. (2) is that of the corollary, `PassesGammaTest`.

## Inputs
* `ε` – half width of the target box

## Hypotheses
* `hε` – the half width is positive

## Conclusion
* the test fails although the box lies in the range exactly when the half width is at most two

## References

* [1] A. Goldsztejn and L. Jaulin. "Inner approximation of the range of vector-valued
      functions". Reliable Computing, 14:1-23, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Example 4.1]: `y ⊆ range(f, x)` iff `ε ≤ 2`, and (2) fails for every `ε > 0`. -/
theorem gammaTest_rotation_example {ε : ℝ} (hε : 0 < ε) : -- --- CONCL ---
    ¬ PassesGammaTest (fun x => !![1, 1; -1, 1] *ᵥ x) 0 (fun _ => -2) (fun _ => 2)
        !![1, 1; -1, 1] !![1, 1; -1, 1] (fun _ => -ε) (fun _ => ε) ∧
      (Icc (fun _ : Fin 2 => -ε) (fun _ => ε) ⊆
        (fun x => !![1, 1; -1, 1] *ᵥ x) '' Icc (fun _ : Fin 2 => (-2 : ℝ)) (fun _ => 2) ↔
        ε ≤ 2) := by -- --- PROOF ---
  have hyε : (![ε, 0] : Fin 2 → ℝ) ∈ Icc (fun _ : Fin 2 => -ε) (fun _ => ε) := by
    constructor <;> intro i <;> fin_cases i <;> simp <;> linarith
  have hyε' : (![ε, -ε] : Fin 2 → ℝ) ∈ Icc (fun _ : Fin 2 => -ε) (fun _ => ε) := by
    constructor <;> intro i <;> fin_cases i <;> simp <;> linarith
  refine ⟨fun h => ?_, ⟨fun h => ?_, fun h y hy => ?_⟩⟩
  · -- row 0 at `y₀ = ε`, `v₁ = -2` leaves the box
    have hv : (![0, -2] : Fin 2 → ℝ) ∈ Icc (fun _ : Fin 2 => (-2 : ℝ)) (fun _ => 2) := by
      constructor <;> intro i <;> fin_cases i <;> simp
    have := h _ hyε !![1, 1; -1, 1] (fun i j => ⟨le_rfl, le_rfl⟩) _ hv 0
    have h0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by
      ext j; fin_cases j <;> simp
    simp [h0] at this
    linarith [this.2]
  · -- `y = (ε, -ε)` has the single preimage `(ε, 0)`
    obtain ⟨x, hx, hxy⟩ := h hyε'
    have h0 := congrFun hxy 0
    have h1 := congrFun hxy 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    have := hx.2 0
    simp at this
    linarith
  · -- `x = ½ (y₀ - y₁, y₀ + y₁)`
    have h0 := hy.1 0
    have h1 := hy.1 1
    have h0' := hy.2 0
    have h1' := hy.2 1
    refine ⟨![(y 0 - y 1) / 2, (y 0 + y 1) / 2], ?_, ?_⟩
    · constructor <;> intro i <;> fin_cases i <;> simp <;> linarith
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
