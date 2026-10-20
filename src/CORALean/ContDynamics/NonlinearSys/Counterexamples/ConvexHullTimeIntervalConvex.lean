module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# The time-interval inner set of L-CSS 2024 fails for a convex initial set too

[1, Prop. 2] claims `conv((X₀ ⊖ C) ⊖ R̂_err, R̂(Δt) ⊖ C) + 2c ⊆ R([0, Δt])` for a compact, nonempty
`X₀`; `convexHull_timeInterval_counterexample` refutes it for a nonconvex `X₀`, this file for a
box. For the shear `ẋ = (x₂, 0)`, `A² = 0`, the linearization is exact, so `R̂_err` (13) and `C`
(17) vanish, `c = 0`, and (23) reads `conv(X₀ ∪ e^{AΔt} X₀) ⊆ R([0, Δt])`. For
`X₀ = [-1/10, 1/10] × [-1, 1]`, `Δt = 1`, the run from `x₀` ends at `(x₀₁ + x₀₂, x₀₂)`;
`(1/2, 0)` is the midpoint of `(0, -1) ∈ X₀` and `e^{A}(0, 1) = (1, 1)`, and a run through it
starts on `x₂ = 0`, where it does not move. The printed proof applies [1, Lemma 1] to
`conv(X₀, R_aff(Δt))`, whose points need not lie on a chord `[x₀, e^{A}x₀]`.

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
-- Last update:   ---
-- Reviewed:      20-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2] fails for the shear `ẋ = (x₂, 0)` from the box `[-1/10, 1/10] × [-1, 1]`:
the box is convex, compact and nonempty, the run from `x₀` ends at `e^{A} x₀ = (x₀₁ + x₀₂, x₀₂)`,
`(1/2, 0)` is in the hull of `X₀` and `e^{A} X₀`, and on no run over `[0, 1]`. -/
theorem convexHull_timeInterval_convex_counterexample : -- --- CONCL ---
    let X₀ : Set (Fin 2 → ℝ) := Icc ![-1 / 10, -1] ![1 / 10, 1]
    let eA : (Fin 2 → ℝ) → Fin 2 → ℝ := fun x => ![x 0 + x 1, x 1]
    Convex ℝ X₀ ∧ IsCompact X₀ ∧ X₀.Nonempty ∧
      (∀ x₀ ∈ X₀, ∀ x : ℝ → Fin 2 → ℝ, x 0 = x₀ →
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x ![x t 1, 0] (Icc 0 1) t) → x 1 = eA x₀) ∧
      ![1 / 2, 0] ∈ convexHull ℝ (X₀ ∪ eA '' X₀) ∧
      ∀ x₀ ∈ X₀, ∀ x : ℝ → Fin 2 → ℝ, x 0 = x₀ →
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x ![x t 1, 0] (Icc 0 1) t) →
        ∀ t ∈ Icc (0 : ℝ) 1, x t ≠ ![1 / 2, 0] := by -- --- PROOF ---
  intro X₀ eA
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
  refine ⟨convex_Icc _ _, isCompact_Icc, nonempty_Icc.mpr ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · -- the run ends at `e^{A} x₀`
    intro x₀ _ x hx0 hder
    obtain ⟨h1, h0⟩ := hrun x hder 1 ⟨zero_le_one, le_rfl⟩
    ext i; fin_cases i <;> simp [eA, h1, h0, hx0]
  · -- the midpoint of `(0, -1) ∈ X₀` and `(1, 1) = e^{A}(0, 1)`
    have h0 : (![0, -1] : Fin 2 → ℝ) ∈ X₀ ∪ eA '' X₀ :=
      Or.inl ((hmem _).mpr ⟨by simp; norm_num, by simp⟩)
    have h1 : (![1, 1] : Fin 2 → ℝ) ∈ X₀ ∪ eA '' X₀ := by
      refine Or.inr ⟨![0, 1], (hmem _).mpr ⟨by simp; norm_num, by simp⟩, ?_⟩
      ext i; fin_cases i <;> simp [eA]
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
