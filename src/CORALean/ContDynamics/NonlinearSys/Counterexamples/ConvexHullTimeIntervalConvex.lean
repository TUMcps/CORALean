module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# The time-interval inner set of L-CSS 2024 fails for a convex initial set too

[1, Prop. 2] claims `conv((X₀ ⊖ C) ⊖ R̂_err, R̂(Δt) ⊖ C) + 2c ⊆ R([0, Δt])` for a compact, nonempty
`X₀`; `convexHull_timeInterval_counterexample` refutes it for a nonconvex `X₀`, this file for a
box. For the shear `ẋ = (x₂, 0)`, `A = [0 1; 0 0]`, `A² = 0`, `e^{A} = I + A`; at a Taylor order
`η ≥ 1`, `R̂_err` (13) and `C` (17) vanish and `c = 0` (derived in `InnerMinkDiffTimeInterval`),
so (23) reads `conv(X₀ ∪ e^{AΔt} X₀) ⊆ R([0, Δt])`; at `η = 0`, `C = [-1, 1] × {0}` empties both
differences and (23) holds. For `X₀ = [-1/10, 1/10] × [-1, 1]`, `Δt = 1`, `(1/2, 0)` is the
midpoint of `(0, -1) ∈ X₀` and `e^{A}(0, 1) = (1, 1)`; a run through it starts on `x₂ = 0`, where
it does not move. The printed proof applies [1, Lemma 1] off the chords `[x₀, e^{A}x₀]`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a point of the hull of a convex box and its sheared image is reached by no run

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   21-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Set

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2] fails for the shear `ẋ = (x₂, 0)` from the box `[-1/10, 1/10] × [-1, 1]`:
`e^{A} = I + A`, the box is convex, compact and nonempty, the run from `x₀` ends at `e^{A} x₀`,
`(1/2, 0)` is in the hull of `X₀` and `e^{A} X₀`, and on no run over `[0, 1]`. -/
theorem convexHull_timeInterval_convex_counterexample : -- --- CONCL ---
    let X₀ : Set (Fin 2 → ℝ) := Icc ![-1 / 10, -1] ![1 / 10, 1]
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    exp A = 1 + A ∧ Convex ℝ X₀ ∧ IsCompact X₀ ∧ X₀.Nonempty ∧
      (∀ x₀ ∈ X₀, ∀ x : ℝ → Fin 2 → ℝ, x 0 = x₀ →
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x ![x t 1, 0] (Icc 0 1) t) → x 1 = exp A *ᵥ x₀) ∧
      ![1 / 2, 0] ∈ convexHull ℝ (X₀ ∪ (exp A *ᵥ ·) '' X₀) ∧
      ∀ x₀ ∈ X₀, ∀ x : ℝ → Fin 2 → ℝ, x 0 = x₀ →
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x ![x t 1, 0] (Icc 0 1) t) →
        ∀ t ∈ Icc (0 : ℝ) 1, x t ≠ ![1 / 2, 0] := by -- --- PROOF ---
  intro X₀ A
  -- `e^{A} = I + A`, as `A² = 0`
  have hA2 : A ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A, sq, Matrix.mul_apply, Fin.sum_univ_two]
  have hexp : exp A = 1 + A := by
    rw [exp_eq_tsum ℝ]
    show ∑' i : ℕ, ((i.factorial : ℝ)⁻¹) • A ^ i = 1 + A
    rw [tsum_eq_sum (s := Finset.range 2) fun b hb => by
      rw [pow_eq_zero_of_le (by simp at hb; omega) hA2, smul_zero]]
    simp [Finset.sum_range_succ]
  -- `e^{A} x = (x₁ + x₂, x₂)`
  have heA : ∀ y : Fin 2 → ℝ, exp A *ᵥ y = ![y 0 + y 1, y 1] := fun y => by
    rw [hexp, Matrix.add_mulVec, Matrix.one_mulVec]
    ext i; fin_cases i <;> simp [A, Matrix.vecHead, Matrix.vecTail]
  -- a function with zero derivative on `[0, 1]` is constant there
  have hconst : ∀ g : ℝ → ℝ, (∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g 0 (Icc 0 1) s) →
      ∀ t ∈ Icc (0 : ℝ) 1, g t = g 0 := fun g hd =>
    constant_of_has_deriv_right_zero (fun s hs => (hd s hs).continuousWithinAt)
      (fun s hs => (hd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)))
  -- every run is `x t = (x₀₁ + t x₀₂, x₀₂)` on `[0, 1]`
  have hrun : ∀ x : ℝ → Fin 2 → ℝ,
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x ![x t 1, 0] (Icc 0 1) t) →
      ∀ t ∈ Icc (0 : ℝ) 1, x t 1 = x 0 1 ∧ x t 0 = x 0 0 + t * x 0 1 := by
    intro x hder
    have h1 : ∀ t ∈ Icc (0 : ℝ) 1, x t 1 = x 0 1 :=
      hconst (fun s => x s 1) fun s hs => by simpa using hasDerivWithinAt_pi.mp (hder s hs) 1
    have h0 : ∀ t ∈ Icc (0 : ℝ) 1, x t 0 - t * x 0 1 = x 0 0 - 0 * x 0 1 :=
      hconst (fun s => x s 0 - s * x 0 1) fun s hs => by
        -- `x₁ - t x₀₂` has derivative `x₂ - x₀₂ = 0`
        have hx : HasDerivWithinAt (fun s => x s 0) (x s 1) (Icc 0 1) s := by
          simpa using hasDerivWithinAt_pi.mp (hder s hs) 0
        have h2 : HasDerivWithinAt (fun s : ℝ => s * x 0 1) (1 * x 0 1) (Icc 0 1) s :=
          (hasDerivWithinAt_id s (Icc 0 1)).mul_const (x 0 1)
        have h3 : HasDerivWithinAt (fun s => x s 0 - s * x 0 1) (x s 1 - 1 * x 0 1)
            (Icc 0 1) s := hx.sub h2
        rwa [h1 s hs, one_mul, sub_self] at h3
    exact fun t ht => ⟨h1 t ht, by linarith [h0 t ht]⟩
  -- membership in the box, coordinatewise
  have hmem : ∀ y : Fin 2 → ℝ, y ∈ X₀ ↔ y 0 ∈ Icc (-1 / 10) (1 / 10) ∧ y 1 ∈ Icc (-1) 1 := by
    intro y
    simp only [X₀, mem_Icc, Pi.le_def, Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    tauto
  -- `X₀` is a box, convex, compact and nonempty
  refine ⟨hexp, convex_Icc _ _, isCompact_Icc, nonempty_Icc.mpr ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · -- the run ends at `e^{A} x₀`
    intro x₀ _ x hx0 hder
    obtain ⟨h1, h0⟩ := hrun x hder 1 ⟨zero_le_one, le_rfl⟩
    rw [heA]
    ext i; fin_cases i <;> simp [h1, h0, hx0]
  · -- the midpoint of `(0, -1) ∈ X₀` and `(1, 1) = e^{A}(0, 1)`
    have h0 : (![0, -1] : Fin 2 → ℝ) ∈ X₀ ∪ (exp A *ᵥ ·) '' X₀ :=
      Or.inl ((hmem _).mpr ⟨by simp; norm_num, by simp⟩)
    have h1 : (![1, 1] : Fin 2 → ℝ) ∈ X₀ ∪ (exp A *ᵥ ·) '' X₀ := by
      refine Or.inr ⟨![0, 1], (hmem _).mpr ⟨by simp; norm_num, by simp⟩, ?_⟩
      show exp A *ᵥ ![0, 1] = ![1, 1]
      rw [heA]
      ext i; fin_cases i <;> simp
    refine segment_subset_convexHull h0 h1
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; fin_cases i <;> simp
  · -- a run through `(1/2, 0)` starts on `x₂ = 0` and keeps its first coordinate
    intro x₀ hx₀ x hx0 hder t ht hxt
    obtain ⟨h1, h0⟩ := hrun x hder t ht
    have e1 := congrFun hxt 1
    have e0 := congrFun hxt 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    rw [hx0] at h1 h0
    have hb := ((hmem x₀).mp hx₀).1
    -- so `x₀₂ = 0` and `x₀₁ = 1/2`, outside `[-1/10, 1/10]`
    rw [e1] at h1
    rw [e0, ← h1, mul_zero, add_zero] at h0
    rw [← h0] at hb
    norm_num at hb

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
