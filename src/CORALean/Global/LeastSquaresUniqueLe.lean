module

public import CORALean.Global.Tensor
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# A unique fit needs as many data points as templates

[1, Sec. 3.1]: "a lower bound for the parameter `w` is given by `⌈0.5(v - 1)⌉`, since one
requires at least `v` data points with `n` values to uniquely identify a matrix `A ∈ ℝⁿˣᵛ`".
If (4) has a unique minimizer, `N = 2w + 1 ≥ v`: with fewer columns than rows `Φ` has a nonzero
`z` with `zᵀ Φ = 0`, and adding `z` to a row of `A` changes nothing of `A Φ`. And `2w + 1 ≥ v` is
`w ≥ ⌈(v - 1)/2⌉`. Uniqueness is what the sentence says; any `N` gives some least-squares fit.

## Inputs
* `Xd` – derivative snapshots
* `Φ` – regressor snapshots
* `A` – minimizing matrix

## Hypotheses
* `hn` – there is at least one output
* `huniq` – the minimizer is unique

## Conclusion
* there are at least as many data points as templates, and the window bound is equivalent

## References

* [1] N. Kochdumper, M. A. Foughali, P. Habermehl and E. Asarin. "Robust Identification of Hybrid
      Automata from Noisy Data". Proceedings of the 28th ACM International Conference on Hybrid
      Systems: Computation and Control, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n v N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3.1]: a unique minimizer of (4) needs `N ≥ v` data points, and `2w + 1 ≥ v` is
`w ≥ ⌈(v - 1)/2⌉`. -/
theorem le_of_leastSquares_unique (Xd : Mat ℝ n N) (Φ : Mat ℝ v N) (A : Mat ℝ n v) (hn : 0 < n)
    (huniq : ∀ B : Mat ℝ n v,
      ∑ i, ∑ a, ((Xd - B * Φ) a i) ^ 2 = ∑ i, ∑ a, ((Xd - A * Φ) a i) ^ 2 → B = A)
    : -- --- CONCL ---
    v ≤ N ∧ ∀ w : ℕ, (v : ℤ) ≤ 2 * w + 1 ↔ ⌈((v : ℝ) - 1) / 2⌉ ≤ w := by -- --- PROOF ---
  refine ⟨?_, fun w => ?_⟩
  · by_contra hlt
    push Not at hlt
    -- a nonzero `z` with `Φᵀ z = 0`, as `Φᵀ` maps `ℝᵛ` into the smaller `ℝᴺ`
    have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := Matrix.mulVecLin Φᵀ)
      (by simpa using hlt)
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz
    -- adding `z` to row `0` of `A` leaves `A Φ` unchanged
    let a₀ : Fin n := ⟨0, hn⟩
    let E : Mat ℝ n v := Matrix.of fun a j => if a = a₀ then z j else 0
    have hEΦ : E * Φ = 0 := by
      ext a i
      have hzi := congrFun hz i
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at hzi
      by_cases ha : a = a₀
      · simp only [E, Matrix.mul_apply, Matrix.of_apply, if_pos ha, Matrix.zero_apply]
        rw [← hzi]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      · simp [E, Matrix.mul_apply, ha]
    -- so `A + E` fits as well, and uniqueness forces `E = 0`
    have hB := huniq (A + E) (by rw [Matrix.add_mul, hEΦ, add_zero])
    apply hz0
    funext j
    have := congrFun (congrFun hB a₀) j
    simp only [Matrix.add_apply, E, Matrix.of_apply, add_eq_left] at this
    exact this
  · rw [Int.ceil_le, Int.cast_natCast]
    constructor
    · intro h
      have : (v : ℝ) ≤ 2 * w + 1 := by exact_mod_cast h
      linarith
    · intro h
      have : (v : ℝ) ≤ 2 * w + 1 := by linarith
      exact_mod_cast this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
