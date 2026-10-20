module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# The time-interval inner set of L-CSS 2024 is not inside the reachable set

[1, Prop. 2] claims `conv((X₀ ⊖ C) ⊖ R̂_err, R̂(Δt) ⊖ C) + 2c ⊆ R([0, Δt])` for a compact, nonempty
`X₀`. For `ẋ = w` the linearization is exact (`A = 0`), so `R̂_err` (13) and `C = F X₀ ⊕ G w` (17)
vanish, `c = 0`, `R̂(Δt) = X₀ + Δt w`, and (23) reads `conv(X₀ ∪ (X₀ + Δt w)) ⊆ X₀ + [0, Δt] w`. For
the two squares `X₀ = ([0, 1/10] ∪ [9/10, 1]) × [0, 1/10]`, `w = (0, 1)`, `Δt = 1`, the point
`(1/2, 1/2)` is the midpoint of `(0, 0)` and `(1, 1)` and so in the hull, and no run reaches it. The
printed proof applies [1, Lemma 1] to `conv(X₀, R_aff(Δt))`, whose points need not be
`x₀ + (t/Δt)(R_aff - x₀)` for one `x₀`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a point of the hull of the initial set and its translate is reached by no run

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      20-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2] fails for `ẋ = (0, 1)` from two squares: `(1/2, 1/2)` is in the hull of `X₀`
and `X₀ + w`, and on no run over `[0, 1]`. -/
theorem convexHull_timeInterval_counterexample : -- --- CONCL ---
    let X₀ : Set (Fin 2 → ℝ) := {x | (x 0 ∈ Icc 0 (1 / 10) ∨ x 0 ∈ Icc (9 / 10) 1) ∧
      x 1 ∈ Icc 0 (1 / 10)}
    let w : Fin 2 → ℝ := ![0, 1]
    ![1 / 2, 1 / 2] ∈ convexHull ℝ (X₀ ∪ (fun x => x + w) '' X₀) ∧
      ∀ x₀ ∈ X₀, ∀ x : ℝ → Fin 2 → ℝ, x 0 = x₀ →
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt x w (Icc 0 1) t) →
        ∀ t ∈ Icc (0 : ℝ) 1, x t ≠ ![1 / 2, 1 / 2] := by -- --- PROOF ---
  intro X₀ w
  refine ⟨?_, fun x₀ hx₀ x hx0 hder t ht hxt => ?_⟩
  · -- the midpoint of `(0, 0) ∈ X₀` and `(1, 1) = (1, 0) + w`
    have h0 : (![0, 0] : Fin 2 → ℝ) ∈ X₀ ∪ (fun x => x + w) '' X₀ :=
      Or.inl ⟨Or.inl ⟨le_refl _, by norm_num⟩, by simp⟩
    have h1 : (![1, 1] : Fin 2 → ℝ) ∈ X₀ ∪ (fun x => x + w) '' X₀ := by
      refine Or.inr ⟨![1, 0], ⟨Or.inr ⟨by simp; norm_num, by simp⟩, by simp⟩, ?_⟩
      ext i; fin_cases i <;> simp [w]
    refine segment_subset_convexHull h0 h1 ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; fin_cases i <;> simp
  · -- the first coordinate is constant along the run
    have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s => x s 0) 0 (Icc 0 1) s :=
      fun s hs => by simpa [w] using hasDerivWithinAt_pi.mp (hder s hs) 0
    have hc : ContinuousOn (fun s => x s 0) (Icc 0 1) := fun s hs => (hd s hs).continuousWithinAt
    have hconst := constant_of_has_deriv_right_zero hc (fun s hs => (hd s
      (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1))) t ht
    have h := congrFun hxt 0
    simp only [hconst, hx0] at h
    rcases hx₀.1 with h' | h' <;> simp at h <;> rw [h] at h' <;> norm_num at h'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
