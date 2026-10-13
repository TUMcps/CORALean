import CORALean.ContDynamics.LinearSysDT.Theorems.Real.IntervalEstimateLeIntervalObserver
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Alg. 1 is not tighter than Eq. 36 without `A - LC ≥ 0`

[1, Thm. 7] states only "the same observer gain and initial conditions" for `x̲ⁱ_k ≤ x̲_k` and
`x̅_k ≤ x̅ⁱ_k`, and its proof uses `A - LC ≥ 0` (Lemma 5 at `A - LC`). In one dimension take
`A = 0`, `C = L = 1`, so `A - LC = -1` (a Schur matrix, an admissible gain), no input and
no noise (`B = E = F = 0`, `W = V = {0}`), `u = y = 0`, and the initial set `X₀ = [-1, 1]`.
Both start at `[-1, 1]`. At `k = 1` the estimate is `[-1, 1]`, the generator `-1` of
`(A - LC) S_x`, while Eq. 36 maps the bounds `x̲ = -1`, `x̅ = 1` to `L(y - C x̲) = 1` and
`L(y - C x̅) = -1`: the lower bound `1` exceeds Alg. 1's `-1`.

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 7] as printed: `A - LC ≥ 0` is not among the hypotheses, and Eq. 36 is no longer
an interval observer. -/
theorem LinearSysDT.intervalEstimate_le_intervalObserver_counterexample :
    ¬ ∀ (n nu ny nw nv : ℕ) (A : Mat ℝ n n) (B : Mat ℝ n nu) (C : Mat ℝ ny n) (E : Mat ℝ n nw)
      (F : Mat ℝ ny nv) (L : Mat ℝ n ny) (X₀ : Zonotope (Vec ℝ n)) (W : Zonotope (Vec ℝ nw))
      (V : Zonotope (Vec ℝ nv)) (wl wu : Vec ℝ nw) (vl vu : Vec ℝ nv) (u : ℕ → Vec ℝ nu)
      (y : ℕ → Vec ℝ ny),
      (∀ w ∈ W.construct, ∀ i, wl i ≤ w i ∧ w i ≤ wu i) →
      (∀ v ∈ V.construct, ∀ i, vl i ≤ v i ∧ v i ≤ vu i) → ∀ (k : ℕ) (i : Fin n),
      let Alg := LinearSysDT.intervalEstimate A B C E F L X₀ W V u y
      let Obs := LinearSysDT.intervalObserver A B C E F L wl wu vl vu (Alg 0).inf (Alg 0).sup u y
      (Obs k).inf i ≤ (Alg k).inf i ∧ (Alg k).sup i ≤ (Obs k).sup i := by -- --- PROOF ---
  intro h
  have hz : ∀ w ∈ (⟨0, 0, fun i => i.elim0⟩ : Zonotope (Vec ℝ 1)).construct, ∀ i : Fin 1,
      (fun _ => (0 : ℝ) : Vec ℝ 1) i ≤ w i ∧ w i ≤ (fun _ => (0 : ℝ) : Vec ℝ 1) i := by
    rintro w ⟨β, _, rfl⟩ i
    simp
  have := (h 1 1 1 1 1 0 0 !![1] 0 0 !![1] ⟨1, 0, fun _ _ => 1⟩ ⟨0, 0, fun i => i.elim0⟩
    ⟨0, 0, fun i => i.elim0⟩ 0 0 0 0 (fun _ => 0) (fun _ => 0) hz hz 1 0)
  have hof : ∀ f : Fin 1 → ℝ, (Entrywise.ofEntry f : Vec ℝ 1) = f := fun _ => rfl
  have hen : ∀ (v : Vec ℝ 1) (i : Fin 1), Entrywise.entry v i = v i := fun _ _ => rfl
  simp [hof, hen, Matrix.vecHead, LinearSysDT.intervalEstimate, LinearSysDT.intervalEstimateState,
    LinearSysDT.intervalEstimateStep, LinearSysDT.intervalObserver, Zonotope.interval,
    Interval.plus, Interval.point, Zonotope.mtimes] at this
  norm_num at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
